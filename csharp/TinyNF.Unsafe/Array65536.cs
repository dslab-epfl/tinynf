using System;

namespace TinyNF.Unsafe
{
    public delegate Span<T> Array65536Allocator<T>(uint size);

    /// <summary>
    /// A 65536-element array that can only be indexed with a ushort, guaranteeing a lack of bounds checks.
    /// This struct is safe iff it is only constructed using the explicit constructor, not the default one.
    /// </summary>
    public readonly unsafe struct Array65536<T>
        where T : unmanaged
    {
        private readonly T* _values;

        public Array65536(Array65536Allocator<T> allocator)
        {
            var allocated = allocator(65536);
            if (allocated.Length < 65536)
            {
                throw new Exception("Allocator did not fulfill its contract");
            }
            _values = (T*)System.Runtime.CompilerServices.Unsafe.AsPointer(ref allocated.GetPinnableReference());
        }

        public int Length => 65536;

        public ref T this[ushort n]
        {
            get
            {
                return ref System.Runtime.CompilerServices.Unsafe.AsRef<T>(_values + n);
            }
        }

        public Span<T> AsSpan()
        {
            return new Span<T>(_values, Length);
        }
    }
}
