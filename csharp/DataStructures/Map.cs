using System;
using System.Collections.Generic;
using TinyNF.Environment;
using TinyNF.Unsafe;
using Hash = System.Int32;

namespace DataStructures
{
    // In theory this class wouldn't need ranged ints, but .NET's JIT is currently not very clever about assertion propagation
    // e.g. (ulong)(uint)x > (ulong)(uint)y does not imply (uint)x > (uint)y for x, y ints
    // and >/>=/==/.. don't always imply each other
    // See e.g. https://github.com/dotnet/runtime/issues/48115
    public readonly ref struct Map<K>
        where K : unmanaged
    {
        private static readonly K MissingKey;

        private struct MapItem
        {
            public int Value;
            public int Chain;
            public Hash KeyHash;
        }

        private readonly int _capacity;
        private readonly Array65536<MapItem> _items;

        public Map(IEnvironment env, int capacity)
        {
            _capacity = GetRealCapacity(capacity);
            _items = new Array65536<MapItem>(env.Allocate<MapItem>);
            if (_capacity > _items.Length)
            {
                throw new Exception("Capacity is too big");
            }
        }

        public readonly bool Get(in K key, ref int outValue)
        {
            /*Hash keyHash = key.GetHashCode(); // TODO? os_memory_hash(key_ptr, map->key_size);
            for (int i = 0; i < _items.Length; i++)
            {
                ushort index = Loop(keyHash, i, _items.Length);
                if (_items[index].Busy && _items[index].KeyHash == keyHash)
                {
                    if (EqualityComparer<K>.Default.Equals(_keys[index], key))
                    {
                        outValue = _items[index].Value;
                        return true;
                    }
                }
                else
                {
                    if (_items[index].Chain == 0)
                    {
                        return false;
                    }
                }
            }
            return false;*/
            throw null!;
        }

        public void Set(in K key, int value)
        {
            /*Hash keyHash = key.GetHashCode();// TODO? os_memory_hash(key_ptr, map->key_size);
            for (int i = 0; i < _items.Length; i++)
            {
                ushort index = Loop(keyHash, i, _items.Length);
                if (!_items[index].Busy)
                {
                    _keys[index] = key;
                    _items[index].KeyHash = keyHash;
                    _items[index].Value = value;
                    return;
                }
                _items[index].Chain++;
            }*/
            throw null!;
        }

        public void Remove(in K key)
        {
            /*Hash keyHash = key.GetHashCode(); // TODO? os_memory_hash(key_ptr, map->key_size);
            for (int i = 0; i < _items.Length; i++)
            {
                ushort index = Loop(keyHash, i, _items.Length);
                if (_items[index].Busy && _items[index].KeyHash == keyHash)
                {
                    if (EqualityComparer<K>.Default.Equals(_keys[index], key))
                    {
                        _items[index].Busy = false;
                        return;
                    }
                }
                _items[index].Chain--;
            }*/
            throw null!;
        }

        private static int GetRealCapacity(int capacity)
        {
            if (capacity == 0)
            {
                return 0;
            }
            int realCapacity = 1;
            while (realCapacity < capacity)
            {
                realCapacity *= 2;
            }
            return realCapacity;
        }

        private static ushort Loop(Hash start, int i, int capacity)
        {
            return (ushort)((start + i) & (capacity - 1));
        }
    }
}
