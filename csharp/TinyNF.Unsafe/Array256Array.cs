using System;

namespace TinyNF.Unsafe
{
    /// <summary>
    /// An array of <see cref="Array256{T}" />.
    /// This struct is safe iff it is only constructed using the explicit constructor, not the default one.
    /// </summary>
    public readonly ref struct Array256Array<T>
        where T : unmanaged
    {
        private readonly RefArray<T> _values;

        public readonly int Length => _values.Length;

        public Array256Array(int length, Func<nuint, Memory<T>> allocator)
        {
            _values = new RefArray<T>(length);
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
                return new Array256<T>(ref _values.Get(n));
            }
            set
            {
                _values.Set(n, ref value.AsRef());
            }
        }
    }
}
