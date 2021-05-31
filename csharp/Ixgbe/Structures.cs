using System.Runtime.InteropServices;

namespace TinyNF.Ixgbe
{
    // Transmit heads must be aligned to 16 bytes, we enforce 64 to put each on its own cache line and avoid contention
    [StructLayout(LayoutKind.Sequential, Size = 64)]
    public struct TransmitHead
    {
        public uint Value;
    }

    [StructLayout(LayoutKind.Sequential)]
    internal struct Descriptor
    {
        public ulong Buffer;
        public ulong Metadata;
    }
}
