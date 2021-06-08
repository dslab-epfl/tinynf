using System;

namespace TinyNF.Environment
{
    public interface IEnvironment
    {
        // Memory
        Memory<T> Allocate<T>(uint size) where T : unmanaged;
        Memory<T> MapPhysicalMemory<T>(nuint addr, uint size) where T : unmanaged;
        nuint GetPhysicalAddress<T>(ref T value);

        // PCI
        uint PciRead(PciAddress address, byte register);
        void PciWrite(PciAddress address, byte register, uint value);

        // Time
        void Sleep(TimeSpan span);
    }
}
