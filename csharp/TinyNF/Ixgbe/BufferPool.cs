using System;
using System.Runtime.CompilerServices;
using TinyNF.Environment;
using TinyNF.Unsafe;

namespace TinyNF.Ixgbe;

internal struct Buffer
{
    private static readonly PacketData _data;
    // Valid buffer that can be used as a default for non-null references
    public static Buffer Fake = new() { Data = new(ref _data) };

    // This is very hacky, but storing a Ref<Buffer> directly requires making this a ref struct,
    // and then we can no longer use it as a generic parameter or through an unsafe pointer,
    // which basically prevents us from doing anything useful with it beyond the absolute basics
    private IntPtr _dataPtr;
    public Ref<PacketData> Data
    {
        get => new(_dataPtr);
        set => _dataPtr = value.Ptr;
    }
    public nuint PhysAddr;
    public ulong Length;
}

internal struct BufferPool
{
    private readonly RefArray<Buffer> Buffers;
    private uint Index;

    public BufferPool(IEnvironment environment, int size)
    {
        var packetData = environment.Allocate<PacketData>(size);
        var allBuffers = environment.Allocate<Buffer>(size);

        Buffers = new(size, n => ref allBuffers.Span[n]);
        Index = (uint)(size - 1);

        for (int n = 0; n < size; n++)
        {
            Buffers.Get(n).Data = new Ref<PacketData>(ref packetData.Span[n]);
            Buffers.Get(n).PhysAddr = environment.GetPhysicalAddress(ref packetData.Span[n]);
        }
    }

    [MethodImpl(MethodImplOptions.AggressiveInlining)]
    public bool Give(ref Buffer buffer)
    {
        Index++;
        // Local variables so the JIT can eliminate bounds checks
        var index = Index;
        var buffers = Buffers;
        if (index < (uint)buffers.Length)
        {
            buffers.Set((int)index, ref buffer);
            return true;
        }

        Index--;
        return false;
    }

    // Slightly weird contract because .NET has no notion of zero-overhead optionals: if this returns 'ref Buffer.Fake' then it failed
    [MethodImpl(MethodImplOptions.AggressiveInlining)]
    public ref Buffer Take()
    {
        // Local variables again
        var index = Index;
        var buffers = Buffers;
        if (index < (uint)buffers.Length)
        {
            ref var result = ref buffers.Get((int)index);
            Index--;
            return ref result;
        }

        return ref Buffer.Fake;
    }
}

