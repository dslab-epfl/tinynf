using System;
using System.Runtime.InteropServices;

namespace TinyNF.Unsafe
{
    /// <summary>
    /// A 256-element array that can only be indexed with a byte, guaranteeing a lack of bounds checks.
    /// This struct is safe iff:
    /// - it is constructed using the explicit constructor, not the default one; and
    /// - the allocator returns a pinned block of memory.
    /// </summary>
    public readonly ref struct Array256<T>
        where T : unmanaged
    {
        private readonly Ref<T> _value;

        public readonly int Length => 256;

        public Array256(Func<int, Memory<T>> allocator)
        {
            var allocated = allocator(256);
            if (allocated.Length < 256)
            {
                throw new Exception("Allocator did not fulfill its contract");
            }
            _value = new Ref<T>(ref allocated.Span[0]);
        }

        // Safe only if the reference points to a block of length >=256
        internal Array256(ref T value)
        {
            _value = new Ref<T>(ref value);
        }

        public readonly ref T this[byte n]
        {
            get
            {
                return ref System.Runtime.CompilerServices.Unsafe.Add(ref _value.Get(), n);
            }
        }

        public readonly Span<T> AsSpan()
        {
            return MemoryMarshal.CreateSpan(ref _value.Get(), Length);
        }

        internal readonly ref T AsRef()
        {
            return ref _value.Get();
        }
    }
}
