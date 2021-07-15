namespace TinyNF.Unsafe
{
    /// <summary>
    /// A reference to a value, i.e., a way to get a 'ref T' field.
    /// This struct is safe iff it is only constructed using the explicit constructor, not the default one.
    /// </summary>
    public readonly unsafe ref struct Ref<T>
        where T : unmanaged
    {
        private readonly T* _value;

        public Ref(ref T value)
        {
            _value = (T*)System.Runtime.CompilerServices.Unsafe.AsPointer(ref value);
        }

        internal Ref(T* value)
        {
            _value = value;
        }

        public ref T Get()
        {
            return ref System.Runtime.CompilerServices.Unsafe.AsRef<T>(_value);
        }

        internal T* AsPointer()
        {
            return _value;
        }
    }
}
