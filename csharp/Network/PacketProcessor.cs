namespace TinyNF.Network
{
    public delegate uint PacketProcessor(ref PacketData data, uint length);
}
