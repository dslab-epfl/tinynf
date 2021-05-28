using System;

namespace TinyNF.Network
{
    /// <summary>
    /// Packet data.
    /// This struct is entirely safe, C# just cannot define it without unsafe yet.
    /// See https://github.com/dotnet/csharplang/blob/main/proposals/fixed-sized-buffers.md
    /// and https://github.com/dotnet/csharplang/issues/1314
    /// </summary>
    public unsafe struct PacketData
    {
        private fixed byte _data[(int)DriverConstants.PacketBufferSize];

        public ref byte this[uint index]
        {
            get
            {
                if (index >= DriverConstants.PacketBufferSize)
                {
                    throw new ArgumentOutOfRangeException(nameof(index));
                }
                return ref _data[index];
            }
        }
    }
}
