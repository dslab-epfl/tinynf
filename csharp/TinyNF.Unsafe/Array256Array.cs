namespace TinyNF.Unsafe
{
    /// <summary>
    /// An array of <see cref="Array256{T}" />.
    /// This struct is entirely safe, C# just cannot define it without unsafe yet. Same remarks as <see cref="RefArray{T}" />.
    /// </summary>
    public readonly unsafe struct Array256Array<T>
        where T : unmanaged
    {
        private readonly T*[] _values;

        public int Length => _values.Length;

        public Array256Array(int length, Array256Allocator<T> allocator)
        {
            _values = new T*[length];
            for (int n = 0; n < length; n++)
            {
                this[n] = new Array256<T>(allocator);
            }
        }

        public Array256<T> this[int n]
        {
            get
            {
                // Safe because anything in _values[n] must have been put there by the setter, which guarantees its length is 256 since it comes from an Array256
                return new Array256<T>(_values[n]);
            }
            set
            {
                _values[n] = value.AsPointer();
            }
        }
    }
}
