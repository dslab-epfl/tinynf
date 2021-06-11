using System;
using TinyNF.Unsafe;

namespace TinyNF
{
    public delegate void PacketProcessor(ref PacketData data, ushort length, Array256<ushort> outputs);

    public delegate void SafePacketProcessor(ref PacketData data, ushort length, Span<ushort> outputs);
}
