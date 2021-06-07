using System;
using System.Runtime.InteropServices;

namespace TinyNF.Unsafe
{
    /// <summary>
    /// Array of references to values.
    /// Only optimized for reading; writing has bounds checks.
    /// This struct is entirely safe, C# just cannot define it without unsafe yet.
    /// </summary>
    /// <remarks>
    /// The reason this struct is safe is that the internal array cannot leak.
    /// That is, the struct effectively imposes 'ref struct' limitations on an array, which makes it safe to have an array of references.
    /// </remarks>
    public unsafe ref struct RefArray<T> where T : unmanaged
    {
        private readonly T*[] _data;

        public int Length => _data.Length;

        public RefArray(int length)
        {
            _data = new T*[length];
        }

        public Span<T> this[int index]
        {
            get
            {
                return new Span<T>(_data[index], 1);
            }
            set
            {
                if (value.Length != 1)
                {
                    throw new ArgumentException("Bad span");
                }
                _data[index] = (T*)System.Runtime.CompilerServices.Unsafe.AsPointer(ref value[0]);
            }
        }

        public Enumerator GetEnumerator()
        {
            return new Enumerator(this);
        }

        public ref struct Enumerator
        {
            private readonly RefArray<T> _array;
            private int _index;

            public Enumerator(RefArray<T> array)
            {
                _array = array;
                _index = -1;
            }

            public ref T Current
            {
                get
                {
                    return ref MemoryMarshal.GetReference(_array[_index]);
                }
            }

            public bool MoveNext()
            {
                _index++;
                return _index < _array.Length;
            }
        }
    }
}
