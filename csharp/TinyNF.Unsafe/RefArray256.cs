using System.Runtime.InteropServices;

namespace TinyNF.Unsafe;

/// <summary>
/// RefArray + Array256 = RefArray256.
/// This struct is safe iff:
/// - it is constructed using the explicit constructor, not the default one; and
/// - the references are all to pinned blocks of memory.
/// </summary>
public readonly unsafe ref struct RefArray256<T>
    where T : unmanaged
{
    public delegate ref T Initializer(byte n);

    private readonly T** _data;

    public readonly int Length => 256;

    public RefArray256(Initializer initializer)
    {
        _data = (T**)NativeMemory.Alloc(256, (nuint)sizeof(T*)); // No freeing of this, oh well
        for (int n = 0; n < 256; n++)
        {
            Set((byte)n, ref initializer((byte)n));
        }
    }

    public readonly ref T Get(byte index)
    {
        return ref System.Runtime.CompilerServices.Unsafe.AsRef<T>(_data[index]);
    }

    public readonly void Set(byte index, ref T value)
    {
        _data[index] = (T*)System.Runtime.CompilerServices.Unsafe.AsPointer(ref value);
    }
}
