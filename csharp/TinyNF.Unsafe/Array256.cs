using System;

namespace TinyNF.Unsafe
{
    public delegate Span<T> Array256Allocator<T>(uint size);

    /// <summary>
    /// A 256-element array that can only be indexed with a byte, guaranteeing a lack of bounds checks.
    /// This struct is safe iff it is only constructed using the explicit constructor, not the default one.
    /// </summary>
    public unsafe readonly ref struct Array256<T>
        where T : unmanaged
    {
        private readonly T* _values;

        public Array256(Array256Allocator<T> allocator)
        {
            var allocated = allocator(256);
            if (allocated.Length < 256)
            {
                throw new Exception("Allocator did not fulfill its contract");
            }
            _values = (T*)System.Runtime.CompilerServices.Unsafe.AsPointer(ref allocated.GetPinnableReference());
        }

        // Safe only if the span is of length >=256
        internal Array256(T* values)
        {
            _values = values;
        }

        public ref T this[byte n]
        {
            get
            {
                return ref System.Runtime.CompilerServices.Unsafe.AsRef<T>(_values + n);
            }
        }

        public Span<T> AsSpan()
        {
            return new Span<T>(_values, 256);
        }

        internal T* AsPointer()
        {
            return _values;
        }
    }
}
