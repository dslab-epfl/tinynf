using System;

namespace TinyNF.Unsafe
{
    /// <summary>
    /// A 65536-element array that can only be indexed with a ushort, guaranteeing a lack of bounds checks.
    /// This struct is safe iff:
    /// - it is constructed using the explicit constructor, not the default one; and
    /// - the allocator returns a pinned block of memory.
    /// </summary>
    public readonly ref struct Array65536<T>
        where T : unmanaged
    {
        private readonly Ref<T> _value;

        public readonly int Length => 65536;

        public Array65536(Func<int, Memory<T>> allocator)
        {
            var allocated = allocator(65536);
            if (allocated.Length < 65536)
            {
                throw new Exception("Allocator did not fulfill its contract");
            }
            _value = new Ref<T>(ref allocated.Span[0]);
        }

        public readonly ref T this[ushort n]
        {
            get
            {
                return ref System.Runtime.CompilerServices.Unsafe.Add(ref _value.Get(), n);
            }
        }
    }
}
