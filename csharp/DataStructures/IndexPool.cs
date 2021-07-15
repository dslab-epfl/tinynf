using System;
using TinyNF.Environment;
using TinyNF.Unsafe;
using Time = System.UInt64;

namespace DataStructures
{
    public ref struct IndexPool
    {
        private readonly Array65536<Time> _timestamps;
        private readonly int _size;
        private readonly Time _expirationTime;
        private ushort _lastBorrowedIndex;

        public IndexPool(IEnvironment env, int size, Time expirationTime)
        {
            _timestamps = new Array65536<Time>(env.Allocate<Time>);
            if (size > _timestamps.Length)
            {
                throw new Exception("Size is too big");
            }
            _size = size;
            _expirationTime = expirationTime;
            _lastBorrowedIndex = 0;

            for (int n = size; n > 0; n--)
            {
                _timestamps[(ushort)(n - 1)] = Time.MaxValue;
            }
        }

        public bool Borrow(Time time, ref int outIndex, ref bool outUsed)
        {
            for (ushort n = _lastBorrowedIndex; n < _size; n++)
            {
                if (_timestamps[n] == Time.MaxValue)
                {
                    _timestamps[n] = time;
                    _lastBorrowedIndex = n;
                    outIndex = n;
                    outUsed = false;
                    return true;
                }
                if (time >= _expirationTime && time - _expirationTime > _timestamps[n])
                {
                    _timestamps[n] = time;
                    _lastBorrowedIndex = n;
                    outIndex = n;
                    outUsed = true;
                    return true;
                }
            }
            for (ushort n = 0; n < _lastBorrowedIndex; n++)
            {
                if (_timestamps[n] == Time.MaxValue)
                {
                    _timestamps[n] = time;
                    _lastBorrowedIndex = n;
                    outIndex = n;
                    outUsed = false;
                    return true;
                }
                if (time >= _expirationTime && time - _expirationTime > _timestamps[n])
                {
                    _timestamps[n] = time;
                    _lastBorrowedIndex = n;
                    outIndex = n;
                    outUsed = true;
                    return true;
                }
            }
            return false;
        }

        public void Refresh(Time time, ushort index)
        {
            _timestamps[index] = time;
        }

        public readonly bool IsUsed(Time time, ushort index)
        {
            if (index >= _size)
            {
                return false;
            }
            if (_timestamps[index] == Time.MaxValue)
            {
                return false;
            }
            if (time >= _expirationTime && time - _expirationTime > _timestamps[index])
            {
                return false;
            }
            return true;
        }

        public void Return(ushort index)
        {
            _timestamps[index] = Time.MaxValue;
        }
    }
}
