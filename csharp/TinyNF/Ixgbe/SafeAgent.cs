using System;
using System.Collections.Generic;
using System.Threading;
using TinyNF.Environment;

namespace TinyNF.Ixgbe
{
    public ref struct SafeAgent
    {
        private readonly Span<PacketData> _packets;
        private readonly Span<Descriptor> _receiveRing;
        private readonly Memory<Descriptor>[] _transmitRings;
        private readonly Span<uint> _receiveTail;
        private readonly Span<TransmitHead> _transmitHeads;
        private readonly Memory<uint>[] _transmitTails;
        private readonly Span<ushort> _outputs;
        private byte _processDelimiter;


        public SafeAgent(IEnvironment env, Device inputDevice, IReadOnlyList<Device> outputDevices)
        {
            _processDelimiter = 0;
            _outputs = env.Allocate<ushort>((uint)outputDevices.Count).Span;

            _packets = env.Allocate<PacketData>(256).Span;

            _transmitRings = new Memory<Descriptor>[outputDevices.Count];
            for (int n = 0; n < _transmitRings.Length; n++)
            {
                _transmitRings[n] = env.Allocate<Descriptor>(256);
                for (int m = 0; m < _transmitRings[n].Length; m++)
                {
                    _transmitRings[n].Span[m].Buffer = Endianness.ToLittle(env.GetPhysicalAddress(ref _packets[m]));
                }
            }

            _receiveRing = _transmitRings[0].Span;
            _receiveTail = inputDevice.SetInput(env, _receiveRing).Span;

            _transmitHeads = env.Allocate<TransmitHead>((uint)outputDevices.Count).Span;
            _transmitTails = new Memory<uint>[outputDevices.Count];
            for (byte n = 0; n < outputDevices.Count; n++)
            {
                _transmitTails[n] = outputDevices[n].AddOutput(env, _transmitRings[n].Span, ref _transmitHeads[n].Value);
            }
        }

        public void Run(SafePacketProcessor processor)
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
                processor(ref _packets[_processDelimiter], length, _outputs);

                ulong rsBit = ((_processDelimiter % DriverConstants.RecyclePeriod) == (DriverConstants.RecyclePeriod - 1)) ? (1ul << (24 + 3)) : 0ul;
                for (int r = 0; r < _transmitRings.Length; r++)
                {
                    Volatile.Write(ref _transmitRings[r].Span[_processDelimiter].Metadata, Endianness.ToLittle(_outputs[r] | rsBit | (1ul << (24 + 1)) | (1ul << 24)));
                    _outputs[r] = 0;
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

                    Volatile.Write(ref _receiveTail[0], Endianness.ToLittle((earliestTransmitHead - 1) % DriverConstants.RingSize));
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
