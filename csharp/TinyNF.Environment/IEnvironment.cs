using System;

namespace TinyNF.Environment
{
    public interface IEnvironment
    {
        // Memory
        Memory<T> Allocate<T>(uint count) where T : unmanaged;
        Memory<T> MapPhysicalMemory<T>(ulong addr, uint count) where T : unmanaged; // addr is ulong, not nuint, because PCI BARs are 64-bit
        nuint GetPhysicalAddress<T>(ref T value);

        // PCI
        uint PciRead(PciAddress address, byte register);
        void PciWrite(PciAddress address, byte register, uint value);

        // Time
        void Sleep(TimeSpan span);
    }
}
