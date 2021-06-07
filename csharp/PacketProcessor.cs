using TinyNF.Unsafe;

namespace TinyNF
{
    public delegate uint PacketProcessor(ref PacketData data, uint length, Array256<bool> outputs);
}
