using System.Runtime.InteropServices;

namespace TinyNF.Ixgbe
{
    [StructLayout(LayoutKind.Sequential)]
    internal struct Descriptor
    {
        public ulong Buffer;
        public ulong Metadata;
    }
}
