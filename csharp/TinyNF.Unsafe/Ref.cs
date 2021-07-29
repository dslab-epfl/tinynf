namespace TinyNF.Unsafe
{
    /// <summary>
    /// A reference to a value, i.e., a way to get a 'ref T' field.
    /// This struct is safe iff:
    /// - it is constructed using the explicit constructor, not the default one; and
    /// - the value it points to is pinned.
    /// </summary>
    /// <remarks>
    /// This _should_ be System.ByReference, which has special handling from the runtime, but it's internal :-(
    /// so instead we have this cheap knockoff, which doesn't work with non-pinned pointers since the runtime knows nothing of it
    /// (we could use Span and its 0th element, but that adds the overhead of a 4-byte Length field)
    /// </remarks>
    public readonly unsafe ref struct Ref<T>
        where T : unmanaged
    {
        private readonly T* _value;

        public Ref(ref T value)
        {
            _value = (T*)System.Runtime.CompilerServices.Unsafe.AsPointer(ref value);
        }

        public readonly ref T Get()
        {
            return ref System.Runtime.CompilerServices.Unsafe.AsRef<T>(_value);
        }
    }
}
