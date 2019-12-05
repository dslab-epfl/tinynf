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

local DEFAULT_DURATION = 5 -- seconds

local RATE_MIN   = 0 -- Mbps
local RATE_MAX   = 10000 -- Mbps

local HEATUP_DURATION = 5 -- seconds
local HEATUP_RATE     = 100 -- Mbps

local LATENCY_LOAD_RATE   = 1000 -- Mbps
local LATENCY_FLOWS_COUNT = 1000 -- flows

local FLOOD_RATE = 10000 -- Mbps

local RESULTS_FILE_NAME = 'bench.result'


-- Arguments for the script
function configure(parser)
  parser:argument("type", "'latency' or 'throughput'.")
  parser:argument("layer", "Layer at which the flows are meaningful."):convert(tonumber)
  parser:option("-d --duration", "Step duration, in seconds."):default(DEFAULT_DURATION):convert(tonumber)
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
-- (this also means the io.write calls are buffered until the task has finished...)
function _latencyTask(txQueue, rxQueue, layer, duration, direction)
  local timestamper = ts:newUdpTimestamper(txQueue, rxQueue)
  local rateLimiter = timer:new(1 / LATENCY_FLOWS_COUNT)
  local lats = {}

  for i = 1, 10 do
    io.write("Attempt " .. i .. " ... ")
    local hist = hist:new()
    local sendTimer = timer:new(duration)
    local counter = 0

    while sendTimer:running() and mg.running() do
      -- Minimum size for these packets is 84
      local packetSize = 84
      hist:update(timestamper:measureLatency(packetSize, function(buf)
        packetInits[direction](buf, packetSize)
        packetConfigs[direction][layer](buf:getUdpPacket(), counter)
        counter = (counter + 1) % LATENCY_FLOWS_COUNT
      end))
      rateLimiter:wait()
      rateLimiter:reset()
    end

    io.write("1%: " .. hist:percentile( 1) .. " / 25%: " .. hist:percentile(25) ..
         " / 50%: " .. hist:percentile(50) .. " / 75%: " .. hist:percentile(75) ..
         " / 95%: " .. hist:percentile(95) .. " / 99%: " .. hist:percentile(99) .. "ns\n")

    lats[i] = hist:percentile(99)
  end

  table.sort(lats)
  return lats[10]
end

-- Starts a latency-measuring task, which returns the 99th percentile latency
function startMeasureLatency(txQueue, rxQueue, layer, duration, counterStart)
  return mg.startTask("_latencyTask", txQueue, rxQueue, layer, duration, counterStart)
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
        counter = counter + 1--(counter + 1) % FLOWS_COUNT
        if counter == FLOWS_COUNT then
          counter = 0
        end
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
    io.write("Sent " .. tx .. " packets but expected at least " .. targetTx .. ", broken benchmark! Did you change the script and add too many per-packet operations?\n")
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
  io.write("Heatup... (" .. HEATUP_DURATION .. " seconds)\n")
  local tasks = {}
  for i, pair in ipairs(queuePairs) do
    -- flow batch size 32 to ensure at least one packet of every flow is not dropped (unless the NF is really broken),
    -- thus NFs such as NATs will have the right mappings after heatup
    tasks[i] = startMeasureThroughput(pair.tx, pair.rx, HEATUP_RATE, layer, HEATUP_DURATION, pair.direction, 32)
    -- ensure the flows are "opened" before their counterparts come from the other direction, for NFs like NATs
    mg.sleepMillis(100)
  end

  for i, task in ipairs(tasks) do
    local loss = tasks[i]:wait()
    if loss == 1 then
      io.write("Heatup " .. queuePairs[i].description .. " did not get any packets back!\n")
      os.exit(1)
    end
  end
end

-- Measure latency under 1G load
function measureLatencyUnderLoad(queuePairs, extraPair, layer, duration)
  heatUp(queuePairs, layer)

  io.write("Measuring latency; you won't see results til the end...\n")

  local throughputTasks = {}
  for i, pair in ipairs(queuePairs) do
    -- latency task does 10 attempts; add 2 seconds as margin
    throughputTasks[i] = startMeasureThroughput(pair.tx, pair.rx, LATENCY_LOAD_RATE, layer, duration * 10 + 2, pair.direction, 1)
  end

  -- Ensure that the throughput tasks are running (leaves us 1 second as margin)
  mg.sleepMillis(1000)

  local latencyTask = startMeasureLatency(extraPair.tx, extraPair.rx, layer, duration, extraPair.direction)

  local loss = 0
  for _, task in ipairs(throughputTasks) do
    loss = loss + task:wait()
  end

  local lat = latencyTask:wait()

  -- We may have been interrupted
  if not mg.running() then
    io.write("Interrupted\n")
    os.exit(0)
  end

  if loss > 0.001 then
    io.write("Too much loss!\n")
    os.exit(1)
  else
    local outFile = io.open(RESULTS_FILE_NAME, "w")
    outFile:write(lat .. "\n")
  end
end

-- Measure latency
function measureLatencyAlone(queuePairs, extraPair, layer, duration)
  heatUp(queuePairs, layer)

  io.write("Measuring latency without load; you won't see results til the end...\n")

  local lat = startMeasureLatency(extraPair.tx, extraPair.rx, layer, duration, extraPair.direction):wait()

  -- We may have been interrupted
  if not mg.running() then
    io.write("Interrupted\n")
    os.exit(0)
  end

  local outFile = io.open(RESULTS_FILE_NAME, "w")
  outFile:write(lat .. "\n")
end

-- Measure max throughput with less than 0.1% loss
function measureMaxThroughputWithLowLoss(queuePairs, _, layer, duration)
  heatUp(queuePairs, layer)

  local upperBound = RATE_MAX
  local lowerBound = RATE_MIN
  local rate = upperBound
  local bestRate = 0
  local bestTx = 0
  for i = 1, 10 do
    io.write("Step " .. i .. ": " .. (#queuePairs * rate) .. " Mbps... ")
    local tasks = {}
    for i, pair in ipairs(queuePairs) do
      tasks[i] = startMeasureThroughput(pair.tx, pair.rx, rate, layer, duration, pair.direction, 1)
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
      local outFile = io.open(RESULTS_FILE_NAME, "w")
      outFile:write(math.floor(#queuePairs * bestRate) .. "\n")
      break
    end
  end
end

function flood(queuePairs, extraPair, layer, duration)
  io.write("Flooding. Stop with Ctrl+C.\n")

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
  if args.type == 'latency' then
    measureFunc = measureLatencyUnderLoad
  elseif args.type == 'latency-alone' then
    measureFunc = measureLatencyAlone
  elseif args.type == 'throughput' then
    measureFunc = measureMaxThroughputWithLowLoss
  elseif args.type == 'flood' then
    measureFunc = flood
  else
    print("Unknown type.")
    os.exit(1)
  end

  measureFunc(queuePairs, extraPair, args.layer, args.duration)
end
