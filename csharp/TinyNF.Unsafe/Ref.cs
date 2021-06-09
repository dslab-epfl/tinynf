using System;
using System.Runtime.InteropServices;

namespace TinyNF.Unsafe
{
    /// <summary>
    /// A reference to a value, i.e., a way to get a 'ref T' field.
    /// "Unsafe" in the sense it uses MemoryMarshal which is unsafe, see e.g. https://github.com/dotnet/runtime/issues/41418
    /// This struct is safe iff it is only constructed using the explicit constructor, not the default one.
    /// </summary>
    public readonly ref struct Ref<T>
    {
        private readonly Span<T> _value;

        public Ref(Span<T> value)
        {
            if (value.Length == 0)
            {
                throw new ArgumentException("Bad span");
            }
            _value = value;
        }

        public ref T Get()
        {
            return ref MemoryMarshal.GetReference(_value);
        }
    }
}
