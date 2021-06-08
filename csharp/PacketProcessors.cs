using System;
using TinyNF.Unsafe;

namespace TinyNF
{
    public delegate void PacketProcessor(ref PacketData data, uint length, Array256<uint> outputs);

    public delegate void SafePacketProcessor(ref PacketData data, uint length, Span<uint> outputs);
}
