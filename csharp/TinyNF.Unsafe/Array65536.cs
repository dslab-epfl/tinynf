using System;

namespace TinyNF.Unsafe
{
    /// <summary>
    /// A 65536-element array that can only be indexed with a ushort, guaranteeing a lack of bounds checks.
    /// This struct is safe iff it is only constructed using the explicit constructor, not the default one.
    /// </summary>
    public readonly ref struct Array65536<T>
        where T : unmanaged
    {
        private readonly Ref<T> _value;

        public Array65536(Func<nuint, Memory<T>> allocator)
        {
            var allocated = allocator(65536);
            if (allocated.Length < 65536)
            {
                throw new Exception("Allocator did not fulfill its contract");
            }
            _value = new Ref<T>(ref allocated.Span[0]);
        }

        public int Length => 65536;

        public ref T this[ushort n]
        {
            get
            {
                return ref System.Runtime.CompilerServices.Unsafe.Add<T>(ref _value.Get(), n);
            }
        }
    }
}
