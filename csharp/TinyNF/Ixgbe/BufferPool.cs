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

    // OVERHEAD: .NET has no concept of zero-overhead option of pointer like Rust,
    // so we pass an extra bool, and we need a ref to something in case the ref is "invalid"
    // (i.e., it should still be safe to deref, just not the correct thing to do in terms of functional correctness)
    // Hopefully inlining takes care of this (but we cannot rely on it)
    [MethodImpl(MethodImplOptions.AggressiveInlining)]
    public ref Buffer Take(out bool valid)
    {
        // Local variables again
        var index = Index;
        var buffers = Buffers;
        if (index < (uint)buffers.Length)
        {
            ref var result = ref buffers.Get((int)index);
            Index--;
            valid = true;
            return ref result;
        }

        valid = false;
        return ref Buffer.Fake;
    }
}

