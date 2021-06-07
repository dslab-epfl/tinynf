using System;
using TinyNF.Unsafe;

namespace TinyNF
{
    public delegate uint PacketProcessor(ref PacketData data, uint length, Array256<bool> outputs);

    public delegate uint SafePacketProcessor(ref PacketData data, uint length, Span<bool> outputs);
}
