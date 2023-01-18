namespace TinyNF.Unsafe;

/// <summary>
/// Array of references to values.
/// Bounds-checked, but with an enumerator allowing the compiler to elide the checks.
/// This struct is safe iff:
/// - it is constructed using the explicit constructor, not the default one; and
/// - the references are all to pinned blocks of memory.
/// </summary>
public readonly unsafe struct RefArray<T>
    where T : unmanaged
{
    public delegate ref T Initializer(int n);

    private readonly T*[] _data;

    public readonly int Length => _data.Length;

    public RefArray(int length, Initializer initializer)
    {
        _data = new T*[length];
        for (int n = 0; n < length; n++)
        {
            Set(n, ref initializer(n));
        }
    }

    public readonly ref T Get(int index)
    {
        return ref System.Runtime.CompilerServices.Unsafe.AsRef<T>(_data[index]);
    }

    public readonly void Set(int index, ref T value)
    {
        _data[index] = (T*)System.Runtime.CompilerServices.Unsafe.AsPointer(ref value);
    }

    public readonly Enumerator GetEnumerator()
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

        public readonly ref T Current
        {
            get
            {
                return ref _array.Get(_index);
            }
        }

        public bool MoveNext()
        {
            _index++;
            return _index < _array.Length;
        }
    }
}
