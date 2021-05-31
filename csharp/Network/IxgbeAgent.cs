using System;
using System.Collections.Generic;
using System.Threading;
using TinyNF.Unsafe;

namespace TinyNF.Network
{
    // 1 input 1 output for now
    // TODO support multiple outputs
    // perhaps we can have an Array256 of a TransmitHead struct with a single uint + a StructLayout(Size = 64)
    // or even a Span of such a struct (doesn't need to be ref, right?) since all checks should be elided by only ever using it in a loop
    public ref struct IxgbeAgent
    {
        private readonly Array256<PacketData> _packets;
        private readonly Array256<Descriptor> _ring;
        private readonly Ref<uint> _receiveTail;
        private readonly Span<TransmitHead> _transmitHeads;
        private readonly RefArray<uint> _transmitTails;
        private byte _processDelimiter;


        public IxgbeAgent(IEnvironment env, IxgbeDevice inputDevice, IReadOnlyList<IxgbeDevice> outputDevices)
        {
            _processDelimiter = 0;

            _packets = new Array256<PacketData>(s => env.Allocate<PacketData>(s).Span);
            _ring = new Array256<Descriptor>(s => env.Allocate<Descriptor>(s).Span);

            for (int n = 0; n < 256; n++)
            {
                _ring[(byte)n].Buffer = Endianness.ToLittle(env.GetPhysicalAddress(ref _packets[(byte)n]));
            }

            _receiveTail = new Ref<uint>(inputDevice.SetInput(env, _ring.AsSpan()));
            _transmitHeads = env.Allocate<TransmitHead>((uint)outputDevices.Count).Span;
            _transmitTails = new RefArray<uint>(outputDevices.Count);
            for (byte n = 0; n < outputDevices.Count; n++)
            {
                _transmitTails[n] = outputDevices[n].AddOutput(env, _ring.AsSpan(), ref _transmitHeads[n].Value);
            }
        }

        public void Run(PacketProcessor processor)
        {
            uint n;
            for (n = 0; n < DriverConstants.FlushPeriod; n++)
            {
                ulong receiveMetadata = Endianness.FromLittle(Volatile.Read(ref _ring[_processDelimiter].Metadata));
                if ((receiveMetadata & (1ul << 32)) == 0)
                {
                    break;
                }

                uint length = (uint)(receiveMetadata & 0xFFFFu);
                uint transmitLength = processor(ref _packets[_processDelimiter], length);

                ulong rsBit = ((_processDelimiter % DriverConstants.RecyclePeriod) == (DriverConstants.RecyclePeriod - 1)) ? (1ul << (24 + 3)) : 0ul;
                Volatile.Write(ref _ring[_processDelimiter].Metadata, Endianness.ToLittle(transmitLength | rsBit | (1ul << (24 + 1)) | (1ul << 24)));

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

                _processDelimiter++;
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
