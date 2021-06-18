using System;
using TinyNF.Unsafe;

namespace TinyNF
{
    public interface IPacketProcessor 
    { 
        void Process(ref PacketData data, ushort length, Array256<ushort> outputs); 
    }

    public interface ISafePacketProcessor
    {
        void Process(ref PacketData data, ushort length, Span<ushort> outputs);
    }
}
