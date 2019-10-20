local ffi     = require "ffi"
local device  = require "device"
local hist    = require "histogram"
local memory  = require "memory"
local mg      = require "moongen"
local stats   = require "stats"
local timer   = require "timer"
local ts      = require "timestamping"


local PACKET_SIZE = 60 -- packets
local BATCH_SIZE = 64 -- packets
local RATE_MIN   = 0 -- Mbps
local RATE_MAX   = 10000 -- Mbps

local HEATUP_DURATION = 5 -- seconds
local HEATUP_RATE     = 20 -- Mbps

local LATENCY_LOAD_RATE = 1000 -- Mbps
local N_PROBE_FLOWS     = 1000

local RESULTS_FILE_NAME = 'results.tsv'


-- Arguments for the script
function configure(parser)
  parser:description("Generates UDP traffic and measures throughput.")
  parser:argument("type", "'latency' or 'throughput'.")
  parser:argument("layer", "Layer at which the flows are meaningful."):convert(tonumber)
  parser:argument("txDev", "Device to transmit from."):convert(tonumber)
  parser:argument("rxDev", "Device to receive from."):convert(tonumber)
  parser:option("-d --duration", "Step duration."):convert(tonumber)
  parser:option("-x --reverse", "Number of flows for reverse traffic, if required."):default(0):convert(tonumber)
end

-- Per-layer functions to configure a packet given a counter;
-- this assumes the total number of flows is <= 65536
local packetConfigs = {
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
}

-- Fills a packet with default values
-- Set the src to the max, so that dst can easily be set to
-- the counter if needed without overlap
function packetInit(buf, packetSize)
  buf:getUdpPacket():fill{
    ethSrc = "FF:FF:FF:FF:FF:FF",
    ethDst = "00:00:00:00:00:00",
    ip4Src = "255.255.255.255",
    ip4Dst = "0.0.0.0",
    udpSrc = 65535,
    udpDst = 0,
    pktLength = packetSize
  }
end

-- Helper function, has to be global because it's started as a task
function _latencyTask(txQueue, rxQueue, layer, flowCount, duration, counterStart)
  -- Ensure that the throughput task is running
  mg.sleepMillis(1000)

  local timestamper = ts:newUdpTimestamper(txQueue, rxQueue)
  local hist = hist:new()
  local sendTimer = timer:new(duration - 1) -- we just slept for a second earlier, so deduce that
  local rateLimiter = timer:new(1 / flowCount) -- ASSUMPTION: The NF is running
  -- with 1 second expiry time, we want new flows' latency
  local counter = 0

  while sendTimer:running() and mg.running() do
    -- Minimum size for these packets is 84
    local packetSize = 84
    hist:update(timestamper:measureLatency(packetSize, function(buf)
      packetInit(buf, packetSize)
      packetConfigs[layer](buf:getUdpPacket(), counterStart + counter)
      counter = (counter + 1) % flowCount
    end))
    rateLimiter:wait()
    rateLimiter:reset()
  end
  
  return hist:median(), hist:standardDeviation()
end

-- Starts a latency-measuring task, which returns (median, stdev)
function startMeasureLatency(txQueue, rxQueue, layer,
                             flowCount, duration, counterStart)
  return mg.startTask("_latencyTask", txQueue, rxQueue,
                      layer, flowCount, duration, counterStart)
end

-- Helper function, has to be global because it's started as a task
function _throughputTask(txQueue, rxQueue, layer, flowCount, duration)
  local mempool = memory.createMemPool(function(buf) packetInit(buf, PACKET_SIZE) end)
  -- "nil" == no output
  local txCounter = stats:newDevTxCounter(txQueue, "nil")
  local rxCounter = stats:newDevRxCounter(rxQueue, "nil")
  local bufs = mempool:bufArray(BATCH_SIZE)
  local packetConfig = packetConfigs[layer]
  local sendTimer = timer:new(duration)
  local counter = 0

  while sendTimer:running() and mg.running() do
    bufs:alloc(PACKET_SIZE)
    for _, buf in ipairs(bufs) do
      packetConfig(buf:getUdpPacket(), counter)
      -- incAndWrap does this in a supposedly fast way;
      -- in practice it's actually slower!
      -- with incAndWrap this code cannot do 10G line rate
      counter = (counter + 1) % flowCount
    end

    bufs:offloadIPChecksums() -- UDP checksum is optional,
    -- let's do the least possible amount of work
    txQueue:send(bufs)
    txCounter:update()
    rxCounter:update()
  end

  txCounter:finalize()
  rxCounter:finalize()
  return txCounter.total, rxCounter.total
end

-- Starts a throughput-measuring task,
-- which returns (#tx, #rx) packets (where rx == tx iff no loss)
function startMeasureThroughput(txQueue, rxQueue, rate, layer,
                                flowCount, duration)
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
      printf("WARNING - Rate %f (corresponding to desired rate %d) too low," ..
               " will be set to 10 instead.", moongenRate, rate)
      moongenRate = 10
    end
    return math.floor(moongenRate)
  end

  txQueue:setRate(moongenRate(rate))
  return mg.startTask("_throughputTask", txQueue, rxQueue,
                      layer, flowCount, duration)
end


-- Heats up with packets at the given layer, with the given size and number of flows.
-- Errors if the loss is over 1%, and ignoreNoResponse is false.
function heatUp(txQueue, rxQueue, layer, flowCount, ignoreNoResponse)
  io.write("Heating up for " .. HEATUP_DURATION .. " seconds at " ..
             HEATUP_RATE .. " Mbps with " .. flowCount .. " flows... ")
  local tx, rx = startMeasureThroughput(txQueue, rxQueue, HEATUP_RATE,
                                        layer, PACKET_SIZE, flowCount,
                                        HEATUP_DURATION):wait()
  local loss = (tx - rx) / tx
  if loss > 0.001 and not ignoreNoResponse then
    io.write("Over 0.1% loss!\n")
    os.exit(1)
  end
  io.write("OK\n")
end

-- Measure latency under 1G load
function measureLatencyUnderLoad(txQ, rxQ, txQ2, rxQ2, txRevQ, rxRevQ,
                                 layer, duration, reverseFlowCount)
  -- It's the same filter set every time
  -- so not setting it on subsequent attempts is OK
  io.write("\n\n!!! IMPORTANT: You can safely ignore the warnings" ..
             " about setting an fdir filter !!!\n\n\n")

  -- Do not change the name and format of this file
  -- unless you change the rest of the scripts that depend on it!
  local outFile = io.open(RESULTS_FILE_NAME, "w")
  outFile:write("#flows\trate (Mbps)\tmedianLat (ns)\tstdevLat (ns)\n")

  -- Latency task waits 1sec for throughput task to have started, so we compensate
  duration = duration + 1

  for _, flowCount in ipairs({60000}) do
    if reverseFlowCount > 0 then
      heatUp(txRevQ, rxRevQ, layer, reverseFlowCount, true)
    end
    heatUp(txQ, rxQ, layer, flowCount, false)

    io.write("Measuring latency for " .. flowCount .. " flows... ")
    local throughputTask = startMeasureThroughput(txQ, rxQ, LATENCY_LOAD_RATE, layer, flowCount, duration)
    local latencyTask = startMeasureLatency(txQ2, rxQ2, layer, N_PROBE_FLOWS, duration, flowCount)

    -- We may have been interrupted
    if not mg.running() then
      io.write("Interrupted\n")
      os.exit(0)
    end

    local tx, rx = throughputTask:wait()
    local median, stdev = latencyTask:wait()
    local loss = (tx - rx) / tx

    if loss > 0.001 then
      io.write("Too much loss!\n")
      outFile:write(flowCount .. "\t" .. "too much loss" .. "\n")
      break
    else
      io.write("median " .. median .. ", stdev " .. stdev .. "\n")
      outFile:write(flowCount .. "\t" .. LATENCY_LOAD_RATE .. "\t" .. median .. "\t" .. stdev .. "\n")
    end
  end
end

-- Measure max throughput with less than 0.1% loss
function measureMaxThroughputWithLowLoss(txQ, rxQ, txQ2, rxQ2, txRevQ, rxRevQ,
                                         layer, duration, reverseFlowCount)
  -- Do not change the name and format of this file
  -- unless you change the rest of the scripts that depend on it!
  local outFile = io.open(RESULTS_FILE_NAME, "w")
  outFile:write("#flows\tMbps\t#packets\t#pkts/s\tloss\n")

  for _, flowCount in ipairs({60000}) do
    if reverseFlowCount > 0 then
      heatUp(txRevQ, rxRevQ, layer, reverseFlowCount, true)
    end

    heatUp(txQ, rxQ, layer, flowCount, false)

    io.write("Running binary search with " .. flowCount .. " flows...\n")
    local upperBound = RATE_MAX
    local lowerBound = RATE_MIN
    local rate = upperBound
    local bestRate = 0
    local bestTx = 0
    local bestLoss = 1
    -- Binary search phase
    for i = 1, 10 do
      io.write("Step " .. i .. ": " .. rate .. " Mbps... ")
      local tx, rx = startMeasureThroughput(txQ, rxQ, rate, layer, flowCount, duration):wait()

      -- We may have been interrupted
      if not mg.running() then
        io.write("Interrupted\n")
        os.exit(0)
      end

      local loss = (tx - rx) / tx
      io.write(tx .. " sent, " .. rx .. " received, loss = " .. loss .. "\n")

      if (loss < 0.001) then
        bestRate = rate
        bestTx = tx
        bestLoss = loss

        lowerBound = rate
        rate = rate + (upperBound - rate)/2
      else
        upperBound = rate
        rate = lowerBound + (rate - lowerBound)/2
      end

      -- Stop if the first step is already successful,
      -- let's not do pointless iterations
      if (i == 10) or (loss < 0.001 and bestRate == upperBound) then
        -- Note that we write 'bestRate' here,
        -- i.e. the last rate with < 0.001 loss, not the current one
        -- (which may cause > 0.001 loss
        --  since our binary search is bounded in steps)
        outFile:write(flowCount .. "\t" .. math.floor(bestRate) .. "\t" .. bestTx .. "\t" ..
                      math.floor(bestTx/duration) .. "\t" .. bestLoss .. "\n")
        break
      end
    end
  end
end

function master(args)
  -- TX device:
  --   2 queues for sending (so that latency can also generate background load)
  --   1 queue for receiving (for reverse traffic)
  -- RX device: same, but reversed
  -- Reverse traffic not available if there's only one port
  local txQ, txQ2, txRevQ, rxQ, rxQ2, rxRevQ
  if args.txDev == args.rxDev then
    local dev = device.config{port = args.txDev, rxQueues = 2, txQueues = 2}
    device.waitForLinks()
    txQ = dev:getTxQueue(0)
    txQ2 = dev:getTxQueue(1)
    txRevQ = nil
    rxQ = dev:getRxQueue(0)
    rxQ2 = dev:getRxQueue(1)
    rxRevQ = nil
  else
    local txDev = device.config{port = args.txDev, rxQueues = 1, txQueues = 2}
    local rxDev = device.config{port = args.rxDev, rxQueues = 2, txQueues = 1}
    device.waitForLinks()
    txQ = txDev:getTxQueue(0)
    txQ2 = txDev:getTxQueue(1)
    txRevQ = rxDev:getTxQueue(0)
    rxQ = rxDev:getRxQueue(0)
    rxQ2 = rxDev:getRxQueue(1)
    rxRevQ = txDev:getRxQueue(0)
  end

  measureFunc = nil
  if args.type == 'latency' then
    measureFunc = measureLatencyUnderLoad
  elseif args.type == 'throughput' then
    measureFunc = measureMaxThroughputWithLowLoss
  else
    print("Unknown type.")
    os.exit(1)
  end

  measureFunc(txQ, rxQ, txQ2, rxQ2, txRevQ, rxRevQ, args.layer, args.duration, args.reverse)
end
