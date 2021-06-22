using System.Runtime.InteropServices;

namespace TinyNF.Ixgbe
{
    [StructLayout(LayoutKind.Sequential, Size = 64)]
    public struct TransmitHead
    {
        public uint Value;
    }
}
