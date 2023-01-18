using System;

namespace TinyNF.Environment
{
    public interface IEnvironment
    {
        // Memory
        // TODO this is dangerous, we need an initializer parameter
        Memory<T> Allocate<T>(int count) where T : unmanaged; // The semantics of this are rather silly: the resulting Memory<T> has an infinite lifetime!
        Memory<T> MapPhysicalMemory<T>(ulong addr, int count) where T : unmanaged; // addr is ulong, not nuint, because PCI BARs are 64-bit
        nuint GetPhysicalAddress<T>(ref T value);

        // PCI
        uint PciRead(PciAddress address, byte register);
        void PciWrite(PciAddress address, byte register, uint value);

        // Time
        void Sleep(TimeSpan span);
    }
}
