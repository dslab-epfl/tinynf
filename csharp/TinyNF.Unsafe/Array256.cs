using System;
using System.Runtime.InteropServices;

namespace TinyNF.Unsafe
{
    public delegate Span<T> Array256Allocator<T>(uint size);

    /// <summary>
    /// A 256-element array that can only be indexed with a byte, guaranteeing a lack of bounds checks.
    /// This struct is safe iff it is only constructed using the explicit constructor, not the default one.
    /// </summary>
    public unsafe ref struct Array256<T>
    {
        internal readonly Span<T> _values;

        public Array256(Array256Allocator<T> allocator)
        {
            _values = allocator(256);
            if (_values.Length < 256)
            {
                throw new Exception("Allocator did not fulfill its contract");
            }
        }

        // Safe only if the span is of length >=256
        internal Array256(Span<T> values)
        {
            _values = values;
        }

        public ref T this[byte n]
        {
            get
            {
                return ref System.Runtime.CompilerServices.Unsafe.Add(ref MemoryMarshal.GetReference(_values), (uint)n); // the explicit cast leads to shorter generated code
            }
        }

        public Span<T> AsSpan()
        {
            return _values;
        }
    }
}
