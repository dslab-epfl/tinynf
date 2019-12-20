local ffi     = require "ffi"
local device  = require "device"
local hist    = require "histogram"
local memory  = require "memory"
local mg      = require "moongen"
local stats   = require "stats"
local timer   = require "timer"
local ts      = require "timestamping"

local PACKET_SIZE = 60 -- packets
local PACKET_BATCH_SIZE = 64 -- packets

local FLOWS_COUNT = 60000 -- flows

local THROUGHPUT_STEPS_DURATION = 30 -- seconds
local THROUGHPUT_STEPS_COUNT = 10 -- number of trials

local RATE_MIN   = 0 -- Mbps
local RATE_MAX   = 10000 -- Mbps

-- heatup needs to open all ports consecutively on a NAT so that reverse packets can go through
local HEATUP_DURATION   = 5 -- seconds
local HEATUP_RATE       = 1000 -- Mbps
local HEATUP_BATCH_SIZE = 64 -- packets

local LATENCY_DURATION = 60 -- seconds
local LATENCY_PACKETS_PER_SECOND = 1000 -- packets; not too much or MoonGen gets very confused
local LATENCY_LOAD_INCREMENT = 500 -- Mbps
local LATENCY_LOAD_PADDING   = 250 -- Mbps; removed from max load when measuring latency

local FLOOD_RATE = 10000 -- Mbps

local RESULTS_FOLDER_NAME = 'results'
local RESULTS_THROUGHPUT_FILE_NAME = 'throughput'
local RESULTS_LATENCIES_FOLDER_NAME = 'latencies'

-- Arguments for the script
function configure(parser)
  parser:argument("type", "'latency' or 'throughput'.")
  parser:argument("layer", "Layer at which the flows are meaningful."):convert(tonumber)
end

-- Helper function to print a histogram as a CSV row: min, max, median, stdev, 99th
function histogramToString(hist)
  return hist:min() .. ", " .. hist:max() .. ", " .. hist:median() .. ", " .. hist:standardDeviation() .. ", " .. hist:percentile(99)
end

-- Helper function to write all histogram values to a file
function dumpHistogram(hist, filename)
  file = io.open(filename, "w")
  for v in hist:samples() do
    for i = 1, v.v do
      file:write(v.k .. "\n")
    end
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
  local sendTimer = timer:new(LATENCY_DURATION)

  local results = {}
  for i = 1, count do
    local hist = hist:new()
    local counter = 0
    while sendTimer:running() and mg.running() do
      -- Minimum size for these packets is 84
      local packetSize = 84
      hist:update(timestamper:measureLatency(packetSize, function(buf)
        packetInits[direction](buf, packetSize)
        packetConfigs[direction][layer](buf:getUdpPacket(), counter)
        counter = (counter + 1) % FLOWS_COUNT
      end, 2)) -- wait 2ms at most before declaring a packet lost, to avoid confusing old packets for new ones
      rateLimiter:wait()
      rateLimiter:reset()
    end
    results[#results+1] = hist
    io.write("[bench] " .. histogramToString(hist) .. "\n")
    mg.sleepMillis(100)
    sendTimer:reset()
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
  local sendTimer = timer:new(duration)
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
  local targetTx = (rate * 1000 * 1000) / ((PACKET_SIZE + 24) * 8) * duration
  return mg.startTask("_throughputTask", txQueue, rxQueue, layer, duration, direction, flowBatchSize, targetTx)
end


-- Heats up at the given layer
function heatUp(queuePairs, layer)
  io.write("[bench] Heating up...\n")
  local tasks = {}
  for i, pair in ipairs(queuePairs) do
    tasks[i] = startMeasureThroughput(pair.tx, pair.rx, HEATUP_RATE, layer, HEATUP_DURATION, pair.direction, HEATUP_BATCH_SIZE)
    -- ensure the flows are "opened" before their counterparts come from the other direction, for NFs like NATs
    mg.sleepMillis(100)
  end

  for i, task in ipairs(tasks) do
    local loss = tasks[i]:wait()
    if loss > 0.01 then
      io.write("[FATAL] Heatup " .. queuePairs[i].description .. " lost " .. (loss * 100) .. "% of packets!\n")
      os.exit(1)
    end
  end
end


-- Measure max throughput with less than 0.1% loss,
-- and latency at lower rates up to max throughput minus 100Mbps
function measureStandard(queuePairs, extraPair, layer)
  heatUp(queuePairs, layer)

  local upperBound = RATE_MAX
  local lowerBound = RATE_MIN
  local rate = upperBound
  local bestRate = 0
  local bestTx = 0
  for i = 1, THROUGHPUT_STEPS_COUNT do
    io.write("[bench] Step " .. i .. ": " .. (#queuePairs * rate) .. " Mbps... ")
    local tasks = {}
    for i, pair in ipairs(queuePairs) do
      tasks[i] = startMeasureThroughput(pair.tx, pair.rx, rate, layer, THROUGHPUT_STEPS_DURATION, pair.direction, 1)
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
  local currentGuess = LATENCY_LOAD_INCREMENT
  while currentGuess < bestRate do
    latencyRates[#latencyRates+1] = currentGuess
    currentGuess = currentGuess + LATENCY_LOAD_INCREMENT
  end
  currentGuess = currentGuess - LATENCY_LOAD_INCREMENT
  if bestRate - LATENCY_LOAD_PADDING > currentGuess then
    latencyRates[#latencyRates+1] = bestRate - LATENCY_LOAD_PADDING
  end
  -- Finish with 0 because it has no background traffic so the flows will expire
  latencyRates[#latencyRates+1] = 0

  local latencyTask = startMeasureLatency(extraPair.tx, extraPair.rx, layer, extraPair.direction, #latencyRates)
  for r, rate in ipairs(latencyRates) do
    io.write("[bench] Measuring latency at rate " .. (rate * #queuePairs) .. "...\n")
    local throughputTasks = {}
    if rate ~= 0 then
      for i, pair in ipairs(queuePairs) do
        throughputTasks[i] = startMeasureThroughput(pair.tx, pair.rx, rate, layer, LATENCY_DURATION, pair.direction, 1)
      end
    end

    local loss = 0
    for _, task in ipairs(throughputTasks) do
      loss = loss + task:wait()
    end

    -- We may have been interrupted
    if not mg.running() then
      io.write("Interrupted\n")
      os.exit(0)
    end

    if (loss / #queuePairs) > 0.001 then
      -- this really should not happen! we know the NF can sustain this!
      io.write("[FATAL] Too much loss! (" .. (loss / #queuePairs) .. ")\n")
      os.exit(1)
    end

    -- the latency task sleeps 100ms inbetween runs, we must match it
    mg.sleepMillis(100)
  end

  local lats = latencyTask:wait()
  for r, rate in ipairs(latencyRates) do
    dumpHistogram(lats[r], RESULTS_FOLDER_NAME .. "/" .. RESULTS_LATENCIES_FOLDER_NAME .. "/" .. (rate * #queuePairs))
  end
end

-- Measure latency without any load
function measureLatencyAlone(queuePairs, extraPair, layer)
  io.write("[bench] Measuring latency without load...\n")
  local lats = startMeasureLatency(extraPair.tx, extraPair.rx, layer, extraPair.direction, 1):wait()
  dumpHistogram(lats[1], RESULTS_FOLDER_NAME .. "/" .. RESULTS_LATENCIES_FOLDER_NAME .. "/0")
end

function flood(queuePairs, extraPair, layer)
  io.write("[bench] Flooding. Stop with Ctrl+C.\n")

  local tasks = {}
  for i, pair in ipairs(queuePairs) do
    tasks[i] = startMeasureThroughput(pair.tx, pair.rx, FLOOD_RATE, layer, 10 * 1000 * 1000, pair.direction, 1) -- 10M seconds counts as forever in my book
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

  -- Thus we need 1 TX + 1 RX queue in each device for throughput, and 1 TX in device 0 / 1 RX in device 1 for latency
  local dev0 = device.config{port = 0, rxQueues = 1, txQueues = 2}
  local dev1 = device.config{port = 1, rxQueues = 2, txQueues = 1}
  device.waitForLinks()

  local queuePairs = {
    [1] = { tx = dev0:getTxQueue(0), rx = dev1:getRxQueue(0), direction = 0, description = "0->1" },
    [2] = { tx = dev1:getTxQueue(0), rx = dev0:getRxQueue(0), direction = 1, description = "1->0" }
  }
  local extraPair = { tx = dev0:getTxQueue(1), rx = dev1:getRxQueue(1), direction = 0, description = "0->1 extra" }

  measureFunc = nil
  if args.type == 'standard' then
    measureFunc = measureStandard
  elseif args.type == 'latency-alone' then
    measureFunc = measureLatencyAlone
  elseif args.type == 'flood' then
    measureFunc = flood
  else
    print("Unknown type.")
    os.exit(1)
  end

  -- lua doesn't have a built-in cross-plat way to do folders
  os.execute("rm -rf '" .. RESULTS_FOLDER_NAME .. "'")
  os.execute("mkdir -p '" .. RESULTS_FOLDER_NAME .. "/" .. RESULTS_LATENCIES_FOLDER_NAME .. "'")

  measureFunc(queuePairs, extraPair, args.layer)
end
