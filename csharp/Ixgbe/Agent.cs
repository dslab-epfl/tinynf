using System;
using System.Collections.Generic;
using System.Threading;
using TinyNF.Environment;
using TinyNF.Unsafe;

namespace TinyNF.Ixgbe
{
    public ref struct Agent
    {
        private readonly Array256<PacketData> _packets;
        private readonly Array256<Descriptor> _receiveRing;
        private readonly MDArray256<Descriptor> _transmitRings;
        private readonly Ref<uint> _receiveTail;
        private readonly Span<TransmitHead> _transmitHeads;
        private readonly RefArray<uint> _transmitTails;
        private byte _processDelimiter;


        public Agent(IEnvironment env, Device inputDevice, IReadOnlyList<Device> outputDevices)
        {
            _processDelimiter = 0;

            _packets = new Array256<PacketData>(s => env.Allocate<PacketData>(s).Span);

            _transmitRings = new MDArray256<Descriptor>(outputDevices.Count, s => env.Allocate<Descriptor>(s).Span);
            _receiveRing = _transmitRings[0];

            for (int n = 0; n < 256; n++)
            {
                _receiveRing[(byte)n].Buffer = Endianness.ToLittle(env.GetPhysicalAddress(ref _packets[(byte)n]));
            }
            _receiveTail = new Ref<uint>(inputDevice.SetInput(env, _receiveRing.AsSpan()));

            _transmitHeads = env.Allocate<TransmitHead>((uint)outputDevices.Count).Span;
            _transmitTails = new RefArray<uint>(outputDevices.Count);
            for (byte n = 0; n < outputDevices.Count; n++)
            {
                _transmitTails[n] = outputDevices[n].AddOutput(env, _transmitRings[n].AsSpan(), ref _transmitHeads[n].Value);
            }
        }

        public void Run(PacketProcessor processor)
        {
            uint n;
            for (n = 0; n < DriverConstants.FlushPeriod; n++)
            {
                ulong receiveMetadata = Endianness.FromLittle(Volatile.Read(ref _receiveRing[_processDelimiter].Metadata));
                if ((receiveMetadata & (1ul << 32)) == 0)
                {
                    break;
                }

                uint length = (uint)(receiveMetadata & 0xFFFFu);
                uint transmitLength = processor(ref _packets[_processDelimiter], length);

                ulong rsBit = ((_processDelimiter % DriverConstants.RecyclePeriod) == (DriverConstants.RecyclePeriod - 1)) ? (1ul << (24 + 3)) : 0ul;
                foreach(var ring in _transmitRings)
                {
                    Volatile.Write(ref ring[_processDelimiter].Metadata, Endianness.ToLittle(transmitLength | rsBit | (1ul << (24 + 1)) | (1ul << 24)));
                }

                _processDelimiter++;

                if (rsBit != 0)
                {
                    uint earliestTransmitHead = _processDelimiter;
                    ulong minDiff = 0xFF_FF_FF_FF_FF_FF_FF_FFul;
                    foreach (ref var headRef in _transmitHeads)
                    {
                        uint head = Endianness.FromLittle(Volatile.Read(ref headRef.Value));
                        ulong diff = head - _processDelimiter;
                        if (diff <= minDiff)
                        {
                            earliestTransmitHead = head;
                            minDiff = diff;
                        }
                    }

                    Volatile.Write(ref _receiveTail.Get(), Endianness.ToLittle((earliestTransmitHead - 1) % DriverConstants.RingSize));
                }
            }
            if (n != 0)
            {
                foreach (ref var tail in _transmitTails)
                {
                    Volatile.Write(ref tail, Endianness.ToLittle(_processDelimiter));
                }
            }
        }
    }
}
