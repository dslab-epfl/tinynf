using System;
using System.Runtime.CompilerServices;
using System.Threading;
using TinyNF.Environment;
using TinyNF.Unsafe;

namespace TinyNF.Ixgbe
{
    internal ref struct QueueRx
    {
        private readonly Array256<Descriptor> _ring;
        private readonly RefArray256<Buffer> _buffers;
        private readonly Ref<BufferPool> _pool;
        private readonly Ref<uint> _receiveTailAddr;
        private byte _next;

        public QueueRx(IEnvironment env, Device device, ref BufferPool pool)
        {
            _ring = new(env.Allocate<Descriptor>);
            _buffers = new(_ => ref Buffer.Fake);

            for (int n = 0; n < _ring.Length; n++)
            {
                ref var buffer = ref pool.Take(out bool valid);
                if (!valid)
                {
                    throw new Exception("Could not get a buffer to initialize the RX queue");
                }
                _ring[(byte)n].Addr = buffer.PhysAddr;
                _ring[(byte)n].Metadata = 0;
                _buffers.Set((byte)n, ref buffer);
            }

            _pool = new(ref pool);
            _receiveTailAddr = new(ref device.SetInput(env, _ring.AsSpan()).Span[0]);
            _next = 0;
        }

        // we have to use a refarray256 here otherwise using this without bounds check would be a huuuuge pain
        [MethodImpl(MethodImplOptions.AggressiveInlining)]
        public byte Batch(RefArray256<Buffer> buffers, byte buffersCount)
        {
            byte rxCount = 0;
            while (rxCount < buffersCount)
            {
                ulong metadata = Endianness.FromLittle(Volatile.Read(ref _ring[_next].Metadata));
                if ((metadata & Device.RxMetadataDD) == 0)
                {
                    break;
                }

                ref var newBuffer = ref _pool.Get().Take(out bool valid);
                if (!valid)
                {
                    break;
                }

                ref var returnedBuffer = ref _buffers.Get(_next);
                buffers.Set(rxCount, ref returnedBuffer);
                returnedBuffer.Length = Device.RxMetadataLength(metadata);

                _buffers.Set(_next, ref newBuffer);
                _ring[_next].Addr = Endianness.ToLittle(newBuffer.PhysAddr);
                _ring[_next].Metadata = Endianness.ToLittle(0);

                _next++; // implicit modulo since it's a byte
                rxCount++;
            }
            if (rxCount > 0)
            {
                Volatile.Write(ref _receiveTailAddr.Get(), Endianness.ToLittle((uint)(_next - 1)));
            }
            return rxCount;
        }
    }
}