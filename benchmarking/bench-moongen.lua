local ffi     = require "ffi"
local device  = require "device"
local histo   = require "histogram"
local memory  = require "memory"
local mg      = require "moongen"
local stats   = require "stats"
local timer   = require "timer"
local ts      = require "timestamping"

local PACKET_SIZE = 60 -- packets
local PACKET_BATCH_SIZE = 64 -- packets

local FLOWS_COUNT = 60000 -- flows

local THROUGHPUT_STEPS_DURATION = 30000 -- milliseconds
local THROUGHPUT_STEPS_COUNT = 10 -- number of trials

local RATE_MIN = 0 -- Mbps
local RATE_MAX = 10000 -- Mbps

-- heatup needs to open all ports consecutively on a NAT so that reverse packets can go through
local HEATUP_DURATION   = 5000 -- milliseconds
local HEATUP_RATE = 100 -- Mbps
local HEATUP_BATCH_SIZE = 8 -- packets

local LATENCY_DURATION = 30000 -- milliseconds
local LATENCY_PACKETS_PER_SECOND = 1000 -- packets; not too much or MoonGen gets very confused
local LATENCY_PACKETS_SIZE = 84 -- bytes, minimum 84
local LATENCY_LOAD_INCREMENT = 500 -- Mbps
local LATENCY_LOAD_PADDING   = 100 -- Mbps; removed from max load when measuring latency
local LATENCY_TIME_PADDING = 50 -- milliseconds; added before and after all latency measurements to smooth measurements

local RESULTS_FOLDER_NAME = 'results'
local RESULTS_THROUGHPUT_FILE_NAME = 'throughput'
local RESULTS_LATENCIES_FOLDER_NAME = 'latencies'

-- Arguments for the script
function configure(parser)
  parser:argument("type", "Benchmark type: standard, standard-single, flood, or debug ones (see source).")
  parser:argument("layer", "Layer at which the flows are meaningful."):convert(tonumber)
  parser:option("-l --latencyload", "Specific total background load for standard latency; if not set, script does from 0 to max tput"):default(-1):convert(tonumber)
  parser:flag("-x --xchange", "Exchange order of devices, in case you messed up your wiring")
  parser:flag("-r --reverseheatup", "Add heatup in reverse, for Maglev-like load balancers; only for standard-single")
end

-- Helper function to summarize latencies: min, max, median, stdev, 99th
function summarizeLatencies(lats)
  if #lats == 0 then
    return "no data"
  end
  local hist = histo:new()
  for _, val in ipairs(lats) do
    hist:update(val)
  end
  return "min: " .. hist:min() .. ", max: " .. hist:max() .. ", median: " .. hist:median() .. ", stdev: " .. hist:standardDeviation() .. ", 99%: " .. hist:percentile(99)
end

-- Helper function to write latencies to a file
function dumpLatencies(lats, filename)
  file = io.open(filename, "w")
  for _, val in ipairs(lats) do
    file:write(val .. "\n")
  end
  file:close()
end

-- Per-direction per-layer functions to configure a packet given a counter;
-- this assumes the total number of flows is <= 65536
local packetConfigs = {
  [0] = {
    [2] = function(pkt, counter)
      pkt.eth.src:set(counter)
      pkt.eth.dst:set(0xFF0000000000 + counter)
    end,
    [3] = function(pkt, counter)
      pkt.ip4.src:set(counter)
    end,
    [4] = function(pkt, counter)
      pkt.udp.src = counter
    end
  },
  [1] = {
    [2] = function(pkt, counter)
      pkt.eth.src:set(0xFF0000000000 + counter)
      pkt.eth.dst:set(counter)
    end,
    [3] = function(pkt, counter)
      pkt.ip4.dst:set(counter)
    end,
    [4] = function(pkt, counter)
      pkt.udp.dst = counter
    end
  }
}
-- Per-direction functions to initialize a packet
local packetInits = {
  [0] = function(buf, packetSize)
    buf:getUdpPacket():fill{
      ethSrc = "FF:FF:FF:FF:FF:FF",
      ethDst = "00:00:00:00:00:00",
      ip4Src = "255.255.255.255",
      ip4Dst = "0.0.0.0",
      udpSrc = 65535,
      udpDst = 0,
      pktLength = packetSize
    }
  end,
  [1] = function(buf, packetSize)
    buf:getUdpPacket():fill{
      ethSrc = "00:00:00:00:00:00",
      ethDst = "FF:FF:FF:FF:FF:FF",
      ip4Src = "0.0.0.0",
      ip4Dst = "255.255.255.255",
      udpSrc = 0,
      udpDst = 65535,
      pktLength = packetSize
    }
  end
}

-- Helper function, has to be global because it's started as a task
-- Note that MoonGen doesn't want us to create more than one timestamper, so we do all iterations inside the task
function _latencyTask(txQueue, rxQueue, layer, direction, count)
  local timestamper = ts:newUdpTimestamper(txQueue, rxQueue)
  local rateLimiter = timer:new(1 / LATENCY_PACKETS_PER_SECOND)
  local sendTimer = timer:new(LATENCY_DURATION / 1000)

  local results = {}
  for i = 1, count do
    mg.sleepMillis(LATENCY_TIME_PADDING)
    sendTimer:reset()

    local lats = {}
    local counter = 0
    local measureFunc = function()
      return timestamper:measureLatency(LATENCY_PACKETS_SIZE, function(buf)
        packetInits[direction](buf, LATENCY_PACKETS_SIZE)
        packetConfigs[direction][layer](buf:getUdpPacket(), counter)
        counter = (counter + 1) % FLOWS_COUNT
      end, 1) -- wait 1ms at most before declaring a packet lost, to avoid confusing old packets for new ones
    end

    measureFunc() -- expire flows if needed, without counting the latency

    while sendTimer:running() and mg.running() do
      lats[#lats+1] = measureFunc()
      rateLimiter:wait()
      rateLimiter:reset()
    end
    results[#results+1] = lats
    io.write("[bench] " .. summarizeLatencies(lats) .. "\n")
    mg.sleepMillis(LATENCY_TIME_PADDING)
  end

  return results
end

-- Starts a latency-measuring task, which returns $count histograms, sleeping 100ms inbetween measurements
function startMeasureLatency(txQueue, rxQueue, layer, direction, count)
  return mg.startTask("_latencyTask", txQueue, rxQueue, layer, direction, count)
end

-- Helper function, has to be global because it's started as a task
function _throughputTask(txQueue, rxQueue, layer, duration, direction, flowBatchSize, targetTx)
  local mempool = memory.createMemPool(function(buf) packetInits[direction](buf, PACKET_SIZE) end)
  -- "nil" == no output
  local txCounter = stats:newDevTxCounter(txQueue, "nil")
  local rxCounter = stats:newDevRxCounter(rxQueue, "nil")
  local bufs = mempool:bufArray(PACKET_BATCH_SIZE)
  local packetConfig = packetConfigs[direction][layer]
  local sendTimer = timer:new(duration / 1000)
  local counter = 0
  local batchCounter = 0

  while sendTimer:running() and mg.running() do
    bufs:alloc(PACKET_SIZE)
    for _, buf in ipairs(bufs) do
      packetConfig(buf:getUdpPacket(), counter)
      batchCounter = batchCounter + 1
      if batchCounter == flowBatchSize then
        batchCounter = 0
        -- incAndWrap does this in a supposedly fast way;
        -- in practice it's actually slower!
        -- with incAndWrap this code cannot do 10G line rate
        counter = (counter + 1) % FLOWS_COUNT
      end
    end

    bufs:offloadIPChecksums() -- UDP checksum is optional, let's do the least possible amount of work
    txQueue:send(bufs)
    txCounter:update()
    rxCounter:update()
  end

  txCounter:finalize()
  rxCounter:finalize()

  local tx = txCounter.total
  local rx = rxCounter.total

  -- Sanity check; it's very easy to change the script and make it too expensive to generate 10 Gb/s
  if mg.running() and tx  < 0.98 * targetTx then
    io.write("[FATAL] Sent " .. tx .. " packets but expected at least " .. targetTx .. ", broken benchmark! Did you change the script and add too many per-packet operations?\n")
    os.exit(1)
  end

  return (tx - rx) / tx
end

-- Starts a throughput-measuring task, which returns the loss (0 if no loss)
function startMeasureThroughput(txQueue, rxQueue, rate, layer, duration, direction, flowBatchSize)
  -- Get the rate that should be given to MoonGen
  -- using packets of the given size to achieve the given true rate
  function moongenRate(rate)
    -- The rate the user wants is in total Mbits/s
    -- But MoonGen will send it as if the packet size
    -- was packetsize+4 (the 4 is for the hardware-offloaded MAC CRC)
    -- when in fact there are 20 bytes of framing on top of that
    -- (preamble, start delimiter, interpacket gap)
    -- Thus we must find the "moongen rate"
    -- at which MoonGen will transmit at the true rate the user wants
    -- Easiest way to do that is to convert in packets-per-second
    -- Beware, we count packets in bytes and rate in bits so we need to convert!
    -- Also, MoonGen internally calls DPDK in which the rate is an uint16_t,
    -- let's avoid floats...
    -- Furthermore, it seems from tests that rates less than 10 are just ignored...
    local byteRate = rate * 1024 * 1024 / 8
    local packetsPerSec = byteRate / (PACKET_SIZE + 24)
    local moongenByteRate = packetsPerSec * (PACKET_SIZE + 4)
    local moongenRate = moongenByteRate * 8 / (1024 * 1024)
    if moongenRate < 10 then
      printf("WARNING - Rate %f (corresponding to desired rate %d) too low, will be set to 10 instead.", moongenRate, rate)
      moongenRate = 10
    end
    return math.floor(moongenRate)
  end

  txQueue:setRate(moongenRate(rate))
  local targetTx = (rate * 1000 * 1000) / ((PACKET_SIZE + 24) * 8) * (duration / 1000)
  return mg.startTask("_throughputTask", txQueue, rxQueue, layer, duration, direction, flowBatchSize, targetTx)
end


-- Heats up at the given layer
function heatUp(queuePair, layer, ignoreloss)
  io.write("[bench] Heating up...\n")
  local task = startMeasureThroughput(queuePair.tx, queuePair.rx, HEATUP_RATE, layer, HEATUP_DURATION, queuePair.direction, HEATUP_BATCH_SIZE)
  local loss = task:wait()
  if not ignoreloss and loss > 0.01 then
    io.write("[FATAL] Heatup lost " .. (loss * 100) .. "% of packets!\n")
    os.exit(1)
  end
end


-- Measure max throughput with less than 0.1% loss,
-- and latency at lower rates up to max throughput minus 100Mbps
function measureStandard(queuePairs, extraPair, args)
  if args.reverseheatup then
    heatUp(queuePairs[99], args.layer, true) -- 99 is a hack, see master function
  end
  heatUp(queuePairs[1], args.layer, false)

  local upperBound = RATE_MAX
  local lowerBound = RATE_MIN
  local rate = upperBound
  local bestRate = 0
  local bestTx = 0
  for i = 1, THROUGHPUT_STEPS_COUNT do
    io.write("[bench] Step " .. i .. ": " .. (#queuePairs * rate) .. " Mbps... ")
    local tasks = {}
    for i, pair in ipairs(queuePairs) do
      tasks[i] = startMeasureThroughput(pair.tx, pair.rx, rate, args.layer, THROUGHPUT_STEPS_DURATION, pair.direction, 1)
    end

    local loss = 0
    for _, task in ipairs(tasks) do
      loss = loss + task:wait()
    end

    loss = loss / #queuePairs

    -- We may have been interrupted
    if not mg.running() then
      io.write("Interrupted\n")
      os.exit(0)
    end

    io.write("loss = " .. loss .. "\n")

    if (loss < 0.001) then
      bestRate = rate
      bestTx = tx
      lowerBound = rate
      rate = rate + (upperBound - rate)/2
    else
      upperBound = rate
      rate = lowerBound + (rate - lowerBound)/2
    end

    -- Stop if the first step is already successful, let's not do pointless iterations
    if (i == 10) or (loss < 0.001 and bestRate == upperBound) then
      -- Note that we write 'bestRate' here, i.e. the last rate with < 0.001 loss, not the current one
      -- (which may cause > 0.001 loss since our binary search is bounded in steps)
      local tputFile = io.open(RESULTS_FOLDER_NAME .. "/" .. RESULTS_THROUGHPUT_FILE_NAME, "w")
      tputFile:write(math.floor(#queuePairs * bestRate) .. "\n")
      tputFile:close()
      break
    end
  end

  local latencyRates = {}
  local currentGuess = 0
  while currentGuess < bestRate do
    latencyRates[#latencyRates+1] = currentGuess
    currentGuess = currentGuess + LATENCY_LOAD_INCREMENT
  end
  currentGuess = currentGuess - LATENCY_LOAD_INCREMENT
  local lastGuess = bestRate - LATENCY_LOAD_PADDING - (LATENCY_PACKETS_SIZE * LATENCY_PACKETS_PER_SECOND / (1000 * 1000)) -- divide to put it in Mbps
  if bestRate - LATENCY_LOAD_PADDING > currentGuess then
    latencyRates[#latencyRates+1] = bestRate - LATENCY_LOAD_PADDING
  end

  -- override if necessary, see description of the parser option
  if args.latencyload ~= -1 then
    latencyRates = {args.latencyload / #queuePairs}
  end

  local latencyTask = startMeasureLatency(extraPair.tx, extraPair.rx, args.layer, extraPair.direction, #latencyRates)
  for r, rate in ipairs(latencyRates) do
    io.write("[bench] Measuring latency at rate " .. (rate * #queuePairs) .. "...\n")
    local throughputTasks = {}
    local loss = 0

    if rate == 0 then
      mg.sleepMillis(LATENCY_DURATION + LATENCY_TIME_PADDING * 2)
    else
      for i, pair in ipairs(queuePairs) do
        throughputTasks[i] = startMeasureThroughput(pair.tx, pair.rx, rate, args.layer, LATENCY_DURATION + LATENCY_TIME_PADDING * 2, pair.direction, 1)
      end
      for _, task in ipairs(throughputTasks) do
        loss = loss + task:wait()
      end
    end

    -- We may have been interrupted
    if not mg.running() then
      io.write("Interrupted\n")
      os.exit(0)
    end

    -- for some reason even the DPDK no-op gets ~0.1% loss sometimes at low rates...
    if (loss / #queuePairs) > 0.002 then
      io.write("[FATAL] Too much loss! (" .. (loss / #queuePairs) .. ")\n")
      os.exit(1)
    end
  end

  local latss = latencyTask:wait()
  for r, rate in ipairs(latencyRates) do
    dumpLatencies(latss[r], RESULTS_FOLDER_NAME .. "/" .. RESULTS_LATENCIES_FOLDER_NAME .. "/" .. (rate * #queuePairs))
  end
end

-- Measure throughput on a single queue pair, only at 10G
function measureThroughputSingle(queuePairs, _, args)
  io.write("[bench] Measuring loss at 10G single direction...")

  local loss = startMeasureThroughput(queuePairs[1].tx, queuePairs[1].rx, 10 * 1000, args.layer, THROUGHPUT_STEPS_DURATION, queuePairs[1].direction, 1):wait()

  io.write(" loss: " .. (loss * 100) .. "%\n")
end

-- Measure latency without any load
function measureLatencyAlone(queuePairs, extraPair, args)
  io.write("[bench] Measuring latency without load...\n")
  local latss = startMeasureLatency(extraPair.tx, extraPair.rx, args.layer, extraPair.direction, 1):wait()
  dumpLatencies(latss[1], RESULTS_FOLDER_NAME .. "/" .. RESULTS_LATENCIES_FOLDER_NAME .. "/0")
end

function flood(queuePairs, extraPair, args)
  io.write("[bench] Flooding. Stop with Ctrl+C.\n")

  local tasks = {}
  for i, pair in ipairs(queuePairs) do
    tasks[i] = startMeasureThroughput(pair.tx, pair.rx, 10 * 1000, args.layer, 10 * 1000 * 1000, pair.direction, 1) -- 10M seconds counts as forever in my book
  end

  for _, task in ipairs(tasks) do
    task:wait()
  end
end

function master(args)
  -- We have 2 devices, and can thus do two kinds of benchmarks:
  --  Throughput: binary-search how much throughput the NF can handle without dropping more than 0.1% of packets,
  --              in both directions at the same time, thus with a maximum of 20 Gb/s
  --  Latency: Measure the one-way latency of the NF, with background traffic of 1 Gb/s in both directions

  local port0 = 0
  local port1 = 1
  if args.xchange then
    port0 = 1
    port1 = 0
  end

  -- Thus we need 1 TX + 1 RX queue in each device for throughput, and 1 TX in device 0 / 1 RX in device 1 for latency
  local dev0 = device.config{port = port0, rxQueues = 1, txQueues = 2}
  local dev1 = device.config{port = port1, rxQueues = 2, txQueues = 1}
  device.waitForLinks()

  local queuePairs = {
    [1] = { tx = dev0:getTxQueue(0), rx = dev1:getRxQueue(0), direction = 0 },
    [2] = { tx = dev1:getTxQueue(0), rx = dev0:getRxQueue(0), direction = 1 }
  }
  local extraPair = { tx = dev0:getTxQueue(1), rx = dev1:getRxQueue(1), direction = 0 }

  measureFunc = nil
  -- Standard benchmark: tput + lats
  if args.type == 'standard' then
    measureFunc = measureStandard
  -- Same, but on 1 link
  elseif args.type == 'standard-single' then
    queuePairs[99] = queuePairs[2] -- stupid hack, pass a 2nd pair but hide it from iteration
    queuePairs[2] = nil
    measureFunc = measureStandard
  -- Flood forever, useful to inspect client behavior
  elseif args.type == 'flood' then
    measureFunc = flood
  -- Just check loss rate at 10G one-way
  elseif args.type == 'debug-throughput-single' then
    measureFunc = measureThroughputSingle
  -- Just check latency without background load
  elseif args.type == 'debug-latency-alone' then
    measureFunc = measureLatencyAlone
  else
    print("Unknown type.")
    os.exit(1)
  end

  if args.reverseheatup and args.type ~= 'standard-single' then
    print("Reverse heatup is only for standard-single")
    os.exit(1)
  end

  -- lua doesn't have a built-in cross-plat way to do folders
  os.execute("rm -rf '" .. RESULTS_FOLDER_NAME .. "'")
  os.execute("mkdir -p '" .. RESULTS_FOLDER_NAME .. "/" .. RESULTS_LATENCIES_FOLDER_NAME .. "'")

  measureFunc(queuePairs, extraPair, args)
end
