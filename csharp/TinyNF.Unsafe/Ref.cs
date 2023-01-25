using System;

namespace TinyNF.Unsafe;

/// <summary>
/// A reference to a value, i.e., a way to get a 'ref T' field.
/// This struct is safe iff:
/// - it is constructed using an explicit constructor, not the default one; and
/// - its IntPtr-based constructor is only used from a .Ptr of an existing Ref; and
/// - it is constructed from a (ref or IntPtr) to a pinned value
/// </summary>
/// <remarks>
/// This exists to allow storing a Ref as a non-ref-struct, which is horribly hacky
/// but needed for arrays of ref to ref structs (see e.g. the buffer pool)
/// </remarks>
public readonly unsafe ref struct Ref<T>
{
    private readonly IntPtr _value;

    public IntPtr Ptr => (IntPtr)_value;

    public Ref(ref T value)
    {
        _value = (IntPtr)System.Runtime.CompilerServices.Unsafe.AsPointer(ref value);
    }

    public Ref(IntPtr value)
    {
        _value = value;
    }

    public readonly ref T Get()
    {
        return ref System.Runtime.CompilerServices.Unsafe.AsRef<T>((void*)_value);
    }
}
