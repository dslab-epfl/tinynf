namespace TinyNF.Unsafe
{
    /// <summary>
    /// A reference to a value, i.e., a way to get a 'ref T' field.
    /// This struct is safe iff it is only constructed using the explicit constructor, not the default one.
    /// </summary>
    public readonly unsafe struct Ref<T>
        where T : unmanaged
    {
        private readonly void* _value;

        public Ref(ref T value)
        {
            _value = System.Runtime.CompilerServices.Unsafe.AsPointer(ref value);
        }

        public ref T Get()
        {
            return ref System.Runtime.CompilerServices.Unsafe.AsRef<T>(_value);
        }
    }
}
