using System;
using System.Threading;
using TinyNF.Environment;
using TinyNF.Unsafe;

namespace TinyNF.Ixgbe
{
    public ref struct Agent
    {
        private readonly Array256<PacketData> _packets;
        private readonly Array256<Descriptor> _receiveRing;
        private readonly Array256Array<Descriptor> _transmitRings;
        private readonly Ref<uint> _receiveTail;
        private readonly Span<TransmitHead> _transmitHeads;
        private readonly RefArray<uint> _transmitTails;
        private readonly Array256<ushort> _outputs; // trade off a tiny bit of unused space for no bounds checks
        private byte _processDelimiter;


        public Agent(IEnvironment env, Device inputDevice, Device[] outputDevices)
        {
            _processDelimiter = 0;
            _outputs = new Array256<ushort>(s => env.Allocate<ushort>(s).Span);

            _packets = new Array256<PacketData>(s => env.Allocate<PacketData>(s).Span);

            _transmitRings = new Array256Array<Descriptor>(outputDevices.Length, s => env.Allocate<Descriptor>(s).Span);
            for (int r = 0; r < _transmitRings.Length; r++)
            {
                for (int n = 0; n < 256; n++)
                {
                    _transmitRings[r][(byte)n].Buffer = Endianness.ToLittle(env.GetPhysicalAddress(ref _packets[(byte)n]));
                }
            }

            _receiveRing = _transmitRings[0];
            _receiveTail = new Ref<uint>(inputDevice.SetInput(env, _receiveRing.AsSpan()).Span);

            _transmitHeads = env.Allocate<TransmitHead>((uint)outputDevices.Length).Span;
            _transmitTails = new RefArray<uint>(outputDevices.Length);
            for (byte n = 0; n < outputDevices.Length; n++)
            {
                _transmitTails[n] = outputDevices[n].AddOutput(env, _transmitRings[n].AsSpan(), ref _transmitHeads[n].Value).Span;
            }
        }

        // Allow the JIT to inline the processor by making it a struct with a method instead of a delegate.
        // The JIT doesn't inline delegates, as far as I know; however, it will generate a specialized version
        // of the method per value type (and one shared version for all reference types), at which point it can inline the ""virtual"" call.
        public void Run<T>(T processor) where T : struct, IPacketProcessor
        {
            nint n;
            for (n = 0; n < DriverConstants.FlushPeriod; n++)
            {
                ulong receiveMetadata = Endianness.FromLittle(Volatile.Read(ref _receiveRing[_processDelimiter].Metadata));
                if ((receiveMetadata & (1ul << 32)) == 0)
                {
                    break;
                }

                ushort length = (ushort)receiveMetadata;
                processor.Process(ref _packets[_processDelimiter], length, _outputs);

                ulong rsBit = ((_processDelimiter % DriverConstants.RecyclePeriod) == (DriverConstants.RecyclePeriod - 1)) ? (1ul << (24 + 3)) : 0ul;

                // not clear why we have to copy _transmitRings here (its only member is an array), but this is necessary for the bounds check to be eliminated
                // using a byte as the index likewise doesn't lead to the bounds check being eliminated
                var _transmitRings = this._transmitRings;
                for (int b = 0; b < _transmitRings.Length; b++)
                {
                    Volatile.Write(ref _transmitRings[b][_processDelimiter].Metadata, Endianness.ToLittle(_outputs[(byte)b] | rsBit | (1ul << (24 + 1)) | (1ul << 24)));
                    _outputs[(byte)b] = 0;
                }

                _processDelimiter++;

                if (rsBit != 0)
                {
                    uint earliestTransmitHead = _processDelimiter;
                    ulong minDiff = ulong.MaxValue;
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
