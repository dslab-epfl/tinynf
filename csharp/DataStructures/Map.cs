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
        private struct MapItem
        {
            public int Index; // 0..65535 pointing into _keys, or -1 for unused
            public int Chain;
            public Hash Hash;
        }

        private readonly int _capacity;
        private readonly Array65536<K> _keys;
        private readonly Array65536<MapItem> _items;

        public Map(IEnvironment env, int capacity)
        {
            _capacity = GetRealCapacity(capacity);
            _keys = new Array65536<K>(env.Allocate<K>);
            _items = new Array65536<MapItem>(env.Allocate<MapItem>);
            if (_capacity > _items.Length)
            {
                throw new Exception("Capacity is too big");
            }
        }

        public readonly bool Get(in K key, ref ushort outIndex)
        {
            Hash keyHash = key.GetHashCode(); // TODO? os_memory_hash(key_ptr, map->key_size);
            for (int i = 0; i < _items.Length; i++)
            {
                ushort index = Loop(keyHash, i, _items.Length);
                if (_items[index].Index >= 0 && _items[index].Hash == keyHash)
                {
                    if (EqualityComparer<K>.Default.Equals(_keys[(ushort)_items[index].Index], key))
                    {
                        outIndex = (ushort)_items[index].Index;
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
            return false;
        }

        public void Set(in K key, ushort keyIndex)
        {
            Hash keyHash = key.GetHashCode();// TODO? os_memory_hash(key_ptr, map->key_size);
            for (int i = 0; i < _items.Length; i++)
            {
                ushort index = Loop(keyHash, i, _items.Length);
                if (_items[index].Index < 0)
                {
                    _keys[keyIndex] = key;
                    _items[index].Index = keyIndex;
                    _items[index].Hash = keyHash;
                    return;
                }
                _items[index].Chain++;
            }
        }

        public void Remove(ushort keyIndex)
        {
            Hash keyHash = _keys[keyIndex].GetHashCode(); // TODO? os_memory_hash(key_ptr, map->key_size);
            for (int i = 0; i < _items.Length; i++)
            {
                ushort index = Loop(keyHash, i, _items.Length);
                if (_items[index].Index == keyIndex)
                {
                    _items[index].Index = -1;
                    return;
                }
                _items[index].Chain--;
            }
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
