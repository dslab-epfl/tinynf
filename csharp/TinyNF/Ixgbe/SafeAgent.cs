using System;
using System.Runtime.CompilerServices;
using System.Threading;
using TinyNF.Environment;

// Safe version of Agent (i.e., does not use any unsafe code even transitively)
// See the comments in Agent for some explanations

namespace TinyNF.Ixgbe
{
    internal interface ISafePacketProcessor
    {
        void Process(ref PacketData data, ushort length, Span<ushort> outputs);
    }

    internal ref struct SafeAgent
    {
        private const uint FlushPeriod = 8;
        private const uint RecyclePeriod = 64;

        private readonly Span<PacketData> _packets;
        private readonly Span<Descriptor> _receiveRing;
        private readonly Memory<Descriptor>[] _transmitRings;
        private readonly Span<uint> _receiveTail;
        private readonly Span<TransmitHead> _transmitHeads;
        private readonly Memory<uint>[] _transmitTails;
        private readonly Span<ushort> _outputs;
        private byte _processDelimiter;


        public SafeAgent(IEnvironment env, Device inputDevice, Device[] outputDevices)
        {
            _processDelimiter = 0;
            _outputs = env.Allocate<ushort>((uint)outputDevices.Length).Span;

            _packets = env.Allocate<PacketData>(Device.RingSize).Span;

            _transmitRings = new Memory<Descriptor>[outputDevices.Length];
            for (int n = 0; n < _transmitRings.Length; n++)
            {
                _transmitRings[n] = env.Allocate<Descriptor>(Device.RingSize);
                for (int m = 0; m < _transmitRings[n].Length; m++)
                {
                    _transmitRings[n].Span[m].Buffer = Endianness.ToLittle(env.GetPhysicalAddress(ref _packets[m]));
                }
            }

            _receiveRing = _transmitRings[0].Span;
            _receiveTail = inputDevice.SetInput(env, _receiveRing).Span;

            _transmitHeads = env.Allocate<TransmitHead>((uint)outputDevices.Length).Span;
            _transmitTails = new Memory<uint>[outputDevices.Length];
            for (byte n = 0; n < outputDevices.Length; n++)
            {
                _transmitTails[n] = outputDevices[n].AddOutput(env, _transmitRings[n].Span, ref _transmitHeads[n].Value);
            }
        }

        [MethodImpl(MethodImplOptions.AggressiveInlining)]
        public void Run<T>(T processor) where T : struct, ISafePacketProcessor
        {
            nint n;
            for (n = 0; n < FlushPeriod; n++)
            {
                ulong receiveMetadata = Endianness.FromLittle(Volatile.Read(ref _receiveRing[_processDelimiter].Metadata));
                if ((receiveMetadata & (1ul << 32)) == 0)
                {
                    break;
                }

                ushort length = (ushort)receiveMetadata;
                processor.Process(ref _packets[_processDelimiter], length, _outputs);

                ulong rsBit = ((_processDelimiter % RecyclePeriod) == (RecyclePeriod - 1)) ? (1ul << (24 + 3)) : 0ul;
                var transmitRings = _transmitRings;
                for (int r = 0; r < transmitRings.Length; r++)
                {
                    Volatile.Write(ref transmitRings[r].Span[_processDelimiter].Metadata, Endianness.ToLittle(_outputs[r] | rsBit | (1ul << (24 + 1)) | (1ul << 24)));
                    _outputs[r] = 0;
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

                    Volatile.Write(ref _receiveTail[0], Endianness.ToLittle(earliestTransmitHead));
                }
            }
            if (n != 0)
            {
                foreach (var tail in _transmitTails)
                {
                    Volatile.Write(ref tail.Span[0], Endianness.ToLittle(_processDelimiter));
                }
            }
        }
    }
}
