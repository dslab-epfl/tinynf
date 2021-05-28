using System;

namespace TinyNF
{
    public interface IEnvironment
    {
        // Memory
        Span<T> Allocate<T>(nuint size);
        Span<T> MapPhysicalMemory<T>(nuint addr, nuint size);
        nuint GetPhysicalAddress<T>(ref T value);
        nuint GetPhysicalAddress<T>(Span<T> span) => GetPhysicalAddress(ref span.GetPinnableReference()); // convenience

        // PCI
        uint PciRead(PciAddress address, byte register);
        void PciWrite(PciAddress address, byte register, uint value);

        // Time
        void Sleep(TimeSpan span);
    }
}
