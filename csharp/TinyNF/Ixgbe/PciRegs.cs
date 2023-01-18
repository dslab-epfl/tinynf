using System.Numerics;
using TinyNF.Environment;

namespace TinyNF.Ixgbe;

internal static class PciRegs
{
    public static byte BAR0_LOW => 0x10;
    public static byte BAR0_HIGH => 0x14;

    public static byte COMMAND => 0x04;
    public static class COMMAND_
    {
        public const uint MEMORY_ACCESS_ENABLE = 1 << 1;
        public const uint BUS_MASTER_ENABLE = 1 << 2;
        public const uint INTERRUPT_DISABLE = 1 << 10;
    }

    public static byte DEVICESTATUS => 0xAA;
    public static class DEVICESTATUS_
    {
        public const uint TRANSACTIONPENDING = 1 << 5;
    }

    public static byte ID => 0x00;

    public static byte PMCSR => 0x44;
    public static class PMCSR_
    {
        public const uint POWER_STATE = 0b0011;
    }


    public static uint ReadField(IEnvironment environment, PciAddress address, byte reg, uint field)
    {
        uint value = environment.PciRead(address, reg);
        int shift = BitOperations.TrailingZeroCount(field);
        return (value & field) >> shift;
    }

    public static bool IsFieldCleared(IEnvironment environment, PciAddress address, byte reg, uint field)
    {
        return ReadField(environment, address, reg, field) == 0;
    }

    public static void SetField(IEnvironment environment, PciAddress address, byte reg, uint field)
    {
        uint oldValue = environment.PciRead(address, reg);
        uint newValue = oldValue | field;
        environment.PciWrite(address, reg, newValue);
    }
}

