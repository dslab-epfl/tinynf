using System;

namespace TinyNF.Environment;

public interface IEnvironment
{
    // Memory
    Memory<T> Allocate<T>(int count) where T : unmanaged; // The semantics of this are rather silly: the resulting Memory<T> has an infinite lifetime!
    Memory<T> MapPhysicalMemory<T>(ulong addr, int count) where T : unmanaged;
    nuint GetPhysicalAddress<T>(ref T value);

    // PCI
    uint PciRead(PciAddress address, byte register);
    void PciWrite(PciAddress address, byte register, uint value);

    // Time
    void Sleep(TimeSpan span);
}
