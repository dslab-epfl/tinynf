﻿using System.Runtime.CompilerServices;
using System.Threading;
using TinyNF.Unsafe;

namespace TinyNF.Network
{
    // 1 input 1 output for now
    public ref struct IxgbeAgent
    {
        private readonly Array256<PacketData> _packets;
        private readonly Array256<Descriptor> _ring;
        private readonly Ref<uint> _receiveTail;
        private readonly Ref<uint> _transmitHead; // TODO: aligned to 16 bytes and on its own cache line
        private readonly Ref<uint> _transmitTail;
        private byte _processDelimiter;


        public IxgbeAgent(IEnvironment env, IxgbeDevice inputDevice, IxgbeDevice outputDevice)
        {
            _processDelimiter = 0;

            _packets = new Array256<PacketData>(env.Allocate<PacketData>);
            _ring = new Array256<Descriptor>(env.Allocate<Descriptor>);

            byte n = 0;
            do
            {
                // Section 7.2.3.2.2 Legacy Transmit Descriptor Format:
                // "Buffer Address (64)", 1st line offset 0
                nuint packetPhysAddr = env.GetPhysicalAddress(ref _packets[n]);
                // INTERPRETATION-MISSING: The data sheet does not specify the endianness of descriptor buffer addresses..
                // Since Section 1.5.3 Byte Ordering states "Registers not transferred on the wire are defined in little endian notation.", we will assume they are little-endian.
                _ring[n].Buffer = Endianness.ToLittle(packetPhysAddr);
                n++;
            } while (n != 0);

            _receiveTail = new Ref<uint>(inputDevice.SetInput(env, _ring.AsSpan()));
            _transmitHead = new Ref<uint>(env.Allocate<uint>(1));
            _transmitTail = new Ref<uint>(outputDevice.AddOutput(env, _ring.AsSpan(), ref _transmitHead.Get()));
        }


        [MethodImpl(MethodImplOptions.AggressiveInlining)] // so that the null check on `processor` can be removed at compile time
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
                else
                {
                    uint length = (uint)(Endianness.FromLittle(receiveMetadata) & 0xFFFFu);
                    uint transmitLength = processor(ref _packets[_processDelimiter], length);

                    ulong rsBit = ((_processDelimiter % DriverConstants.RecyclePeriod) == (DriverConstants.RecyclePeriod - 1)) ? (1ul << (24 + 3)) : 0ul;
                    Volatile.Write(ref _ring[_processDelimiter].Metadata, Endianness.ToLittle(transmitLength | rsBit | (1ul << (24 + 1)) | (1ul << 24)));

                    if (rsBit != 0)
                    {
                        Volatile.Write(ref _receiveTail.Get(), Endianness.ToLittle((Volatile.Read(ref _transmitHead.Get()) - 1) % DriverConstants.RingSize));
                    }

                    _processDelimiter++;
                }
            }
            if (n != 0)
            {
                Volatile.Write(ref _transmitTail.Get(), Endianness.ToLittle(_processDelimiter));
            }
        }
    }
}