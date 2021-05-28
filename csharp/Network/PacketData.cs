namespace TinyNF.Network
{
    // TODO avoid unsafe here; see https://github.com/dotnet/csharplang/blob/main/proposals/fixed-sized-buffers.md
    //      and https://github.com/dotnet/csharplang/issues/1314
    //      can we use StructLayout?
    public unsafe struct PacketData
    {
        private fixed byte _data[(int)DriverConstants.PacketBufferSize];

        public ref byte this[uint index]
        {
            get => ref _data[index];
        }
    }
}
