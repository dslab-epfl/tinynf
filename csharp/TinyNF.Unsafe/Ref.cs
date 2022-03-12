using System;

namespace TinyNF.Unsafe
{
    /// <summary>
    /// A reference to a value, i.e., a way to get a 'ref T' field.
    /// This struct is safe iff:
    /// - it is constructed using an explicit constructor, not the default one; and
    /// - it is constructed from a (ref or IntPtr) to a pinned value
    /// </summary>
    /// <remarks>
    /// This _should_ be System.ByReference, which has special handling from the runtime, but it's internal :-(
    /// so instead we have this cheap knockoff, which doesn't work with non-pinned pointers since the runtime knows nothing of it
    /// (we could use Span and its 0th element, but that adds the overhead of a 4-byte Length field)
    /// 
    /// The IntPtr part is to allow storing a Ref as a non-ref-struct, which is horribly hacky
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
}
