using System;
using System.Runtime.CompilerServices;
using System.Runtime.InteropServices;

namespace TinyNF.Unsafe
{
    public delegate Span<T> Array256Allocator<T>(nuint size);

    /// <summary>
    /// A 256-element array that can only be indexed with a byte, guaranteeing a lack of bounds checks.
    /// This struct is safe iff (1) it is only constructed using the explicit constructor, not the default one, and
    /// (2) the allocator passed to its constructor returns a valid block of memory of size `size * sizeof(T)`.
    /// </summary>
    public unsafe ref struct Array256<T>
    {
        private readonly Span<T> _values;

        public Array256(Array256Allocator<T> allocator)
        {
            _values = allocator(256);
        }

        public ref T this[byte n]
        {
            [MethodImpl(MethodImplOptions.AggressiveInlining)]
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
