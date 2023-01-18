using System;

namespace TinyNF.Unsafe
{
    /// <summary>
    /// A reference to a value, i.e., a way to get a 'ref T' field.
    /// This struct is safe iff:
    /// - it is constructed using an explicit constructor, not the default one; and
    /// - its IntPtr-based constructor is only used from a .Ptr of an existing Ref
    /// </summary>
    /// <remarks>
    /// The IntPtr part is to allow storing a Ref as a non-ref-struct, which is horribly hacky
    /// but needed for arrays of ref to ref structs (see e.g. the buffer pool).
    /// </remarks>
    public readonly unsafe ref struct Ref<T>
    {
        private readonly ref T _value;

        public IntPtr Ptr => (IntPtr)System.Runtime.CompilerServices.Unsafe.AsPointer(ref _value);

        public Ref(ref T value)
        {
            _value = ref value;
        }

        public Ref(IntPtr value)
        {
            _value = System.Runtime.CompilerServices.Unsafe.AsRef<T>((void*)value);
        }

        public readonly ref T Get()
        {
            return ref _value;
        }
    }
}
