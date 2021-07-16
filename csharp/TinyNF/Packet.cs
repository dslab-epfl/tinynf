using TinyNF.Unsafe;

namespace TinyNF
{
    public ref struct Packet
    {
        public readonly Ref<PacketData> Data;
        public readonly ulong Time;
        public readonly ushort Length;
        public readonly byte Device;

        public Packet(ref PacketData data, ulong time, ushort length, byte device)
        {
            Data = new Ref<PacketData>(ref data);
            Time = time;
            Length = length;
            Device = device;
        }
    }
}
