using System;

namespace TinyNF.Unsafe
{
    /// <summary>
    /// Packet data.
    /// This struct is entirely safe, C# just cannot define it without unsafe yet.
    /// See https://github.com/dotnet/csharplang/blob/main/proposals/fixed-sized-buffers.md
    /// and https://github.com/dotnet/csharplang/issues/1314
    /// </summary>
    public unsafe struct PacketData
    {
        public const int Size = 2048;

        private fixed byte _data[Size];

        public ref byte this[uint index]
        {
            get
            {
                if (index >= Size)
                {
                    throw new ArgumentOutOfRangeException(nameof(index));
                }
                return ref _data[index];
            }
        }
    }
}
