using System;
using System.Numerics;
using TinyNF.Environment;

namespace TinyNF.Ixgbe
{
    internal static class PciRegs
    {
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

        // Section 9.3.2 PCIe Configuration Space Summary: "0x10 Base Address Register 0" (32 bit), "0x14 Base Address Register 1" (32 bit)
        // Section 9.3.6.1 Memory and IO Base Address Registers: BAR 0 is 64-bits, thus it's 0-low and 0-high, not 0 and 1
        public static byte BAR0_LOW => 0x10;
        public static byte BAR0_HIGH => 0x14;

        // Section 9.3.3.3 Command Register (16 bit)
        // Section 9.3.3.4 Status Register (16 bit, unused)
        public static byte COMMAND => 0x04;
        public static class COMMAND_
        {
            public const uint MEMORY_ACCESS_ENABLE = 1 << 1;
            public const uint BUS_MASTER_ENABLE = 1 << 2;
            public const uint INTERRUPT_DISABLE = 1 << 10;
        }

        // Section 9.3.10.6 Device Status Register (16 bit)
        // Section 9.3.10.7 Link Capabilities Register (16 bit, unused)
        public static byte DEVICESTATUS => 0xAA;
        public static class DEVICESTATUS_
        {
            public const uint TRANSACTIONPENDING = 1 << 5;
        }

        // Section 9.3.3.1 Vendor ID Register (16 bit)
        // Section 9.3.3.2 Device ID Register (16 bit)
        public static byte ID => 0x00;

        // Section 9.3.7.1.4 Power Management Control / Status Register (16 bit)
        // Section 9.3.7.1.5 PMCSR_BSE Bridge Support Extensions Register (8 bit, hardwired to 0)
        // Section 9.3.7.1.6 Data Register (8 bit, unused)
        public static byte PMCSR => 0x44;
        public static class PMCSR_
        {
            public const uint POWER_STATE = 0b0011;
        }
    }

    internal static class Regs
    {
        public static uint Read(Memory<uint> buffer, uint reg)
        {
            return Endianness.FromLittle(buffer.Span[(int)reg / sizeof(uint)]);
        }

        public static uint ReadField(Memory<uint> buffer, uint reg, uint field)
        {
            uint value = Read(buffer, reg);
            int shift = BitOperations.TrailingZeroCount(field);
            return (value & field) >> shift;
        }

        public static void Write(Memory<uint> buffer, uint reg, uint value)
        {
            buffer.Span[(int)reg / sizeof(uint)] = Endianness.ToLittle(value);
        }

        public static void WriteField(Memory<uint> buffer, uint reg, uint field, uint fieldValue)
        {
            uint oldValue = Read(buffer, reg);
            int shift = BitOperations.TrailingZeroCount(field);
            uint newValue = (oldValue & ~field) | (fieldValue << shift);
            Write(buffer, reg, newValue);
        }

        public static void Clear(Memory<uint> buffer, uint reg)
        {
            Write(buffer, reg, 0);
        }

        public static void ClearField(Memory<uint> buffer, uint reg, uint field)
        {
            WriteField(buffer, reg, field, 0);
        }

        public static void SetField(Memory<uint> buffer, uint reg, uint field)
        {
            uint oldValue = Read(buffer, reg);
            uint newValue = oldValue | field;
            Write(buffer, reg, newValue);
        }

        public static bool IsFieldCleared(Memory<uint> buffer, uint reg, uint field)
        {
            return ReadField(buffer, reg, field) == 0;
        }

        // Section 8.2.3.1.1 Device Control Register
        public static uint CTRL => 0x00000u;
        public static class CTRL_
        {
            public const uint MASTER_DISABLE = 1 << 2;
            public const uint RST = 1 << 26;
        }

        // Section 8.2.3.1.3 Extended Device Control Register
        public static uint CTRLEXT => 0x00018u;
        public static class CTRLEXT_
        {
            public const uint NSDIS = 1 << 16;
        }

        // Section 8.2.3.11.1 Rx DCA Control Register
        public static uint DCARXCTRL(uint n) => n <= 63u ? (0x0100Cu + 0x40u * n) : (0x0D00Cu + 0x40u * (n - 64u));
        public static class DCARXCTRL_
        {
            public const uint UNKNOWN = 1 << 12; // This bit is reserved, has no name, but must be used anyway
        }

        // Section 8.2.3.11.2 Tx DCA Control Registers
        public static uint DCATXCTRL(uint n) => 0x0600Cu + 0x40u * n;
        public static class DCATXCTRL_
        {
            public const uint TX_DESC_WB_RO_EN = 1 << 11;
        }

        // Section 8.2.3.9.2 DMA Tx Control
        public static uint DMATXCTL => 0x04A80u;
        public static class DMATXCTL_
        {
            public const uint TE = 1 << 0;
        }

        // Section 8.2.3.9.1 DMA Tx TCP Max Allow Size Requests
        public static uint DTXMXSZRQ => 0x08100u;
        public static class DTXMXSZRQ_
        {
            public const uint MAX_BYTES_NUM_REQ = 0b0111_1111_1111;
        }

        // Section 8.2.3.2.1 EEPROM/Flash Control Register
        public static uint EEC => 0x10010u;
        public static class EEC_
        {
            public const uint EE_PRES = 1 << 8;
            public const uint AUTO_RD = 1 << 9;
        }

        // Section 8.2.3.5.9 Extended Interrupt Mask Clear Registers
        public static uint EIMC(uint n) => n == 0 ? 0x00888u : (0x00AB0u + 4u * (n - 1u));

        // Section 8.2.3.3.7 Flow Control Configuration
        public static uint FCCFG => 0x03D00u;
        public static class FCCFG_
        {
            public const uint TFCE = 0b0001_1000;
        }

        // Section 8.2.3.3.4 Flow Control Receive Threshold High
        public static uint FCRTH(uint n) => 0x03260u + 4u * n;
        public static class FCRTH_
        {
            public const uint RTH = 0b0111_1111_1111_1110_0000;
        }

        // Section 8.2.3.7.1 Filter Control Register (FCTRL)
        public static uint FCTRL => 0x05080u;
        public static class FCTRL_
        {
            public const uint MPE = 1 << 8;
            public const uint UPE = 1 << 9;
        }

        // Section 8.2.3.7.19 Five tuple Queue Filter
        public static uint FTQF(uint n) => 0x0E600u + 4u * n;
        public static class FTQF_
        {
            public const uint QUEUE_ENABLE = 1u << 31;
        }

        // Section 8.2.3.4.10 Firmware Semaphore Register
        public static uint FWSM => 0x10148u;
        public static class FWSM_
        {
            public const uint EXT_ERR_IND = 0b0001_1111_1000_0000_0000_0000_0000;
        }

        // Section 8.2.3.4.12 PCIe Control Extended Register
        public static uint GCREXT => 0x11050u;
        public static class GCREXT_
        {
            public const uint BUFFERS_CLEAR_FUNC = 1 << 30;
        }

        // Section 8.2.3.22.8 MAC Core Control 0 Register
        public static uint HLREG0 => 0x04240u;
        public static class HLREG0_
        {
            public const uint LPBK = 1 << 15;
        }

        // Section 8.2.3.22.34 MAC Flow Control Register
        public static uint MFLCN => 0x04294u;
        public static class MFLCN_
        {
            public const uint RFCE = 1 << 3;
        }

        // Section 8.2.3.7.10 MAC Pool Select Array
        public static uint MPSAR(uint n) => 0x0A600u + 4u * n;

        // Section 8.2.3.7.7 Multicast Table Array
        public static uint MTA(uint n) => 0x05200u + 4u * n;

        // Section 8.2.3.27.17 PF Unicast Table Array
        public static uint PFUTA(uint n) => 0x0F400u + 4u * n;

        // Section 8.2.3.27.15 PF VM VLAN Pool Filter
        public static uint PFVLVF(uint n) => 0x0F100u + 4u * n;

        // Section 8.2.3.27.16 PF VM VLAN Pool Filter Bitmap
        public static uint PFVLVFB(uint n) => 0x0F200u + 4u * n;

        // Section 8.2.3.8.2 Receive Descriptor Base Address High
        public static uint RDBAH(uint n) => n <= 63u ? (0x01004u + 0x40u * n) : (0x0D004u + 0x40u * (n - 64u));

        // Section 8.2.3.8.1 Receive Descriptor Base Address Low
        public static uint RDBAL(uint n) => n <= 63u ? (0x01000u + 0x40u * n) : (0x0D000u + 0x40u * (n - 64u));

        // Section 8.2.3.8.3 Receive Descriptor Length
        public static uint RDLEN(uint n) => n <= 63u ? (0x01008u + 0x40u * n) : (0x0D008u + 0x40u * (n - 64u));

        // Section 8.2.3.8.8 Receive DMA Control Register
        // INTERPRETATION-MISSING: Bit 0, which is not mentioned in the table, is reserved
        public static uint RDRXCTL => 0x02F00u;
        public static class RDRXCTL_
        {
            public const uint CRC_STRIP = 1 << 1;
            public const uint DMAIDONE = 1 << 3;
            public const uint RSCFRSTSIZE = 0b0011_1110_0000_0000_0000_0000;
            public const uint RSCACKC = 1 << 25;
            public const uint FCOE_WRFIX = 1 << 26;
        }

        // Section 8.2.3.8.5 Receive Descriptor Tail
        public static uint RDT(uint n) => n <= 63u ? (0x01018u + 0x40u * n) : (0x0D018u + 0x40u * (n - 64u));

        // Section 8.2.3.10.2 DCB Transmit Descriptor Plane Control and Status
        public static uint RTTDCS => 0x04900u;
        public static class RTTDCS_
        {
            public const uint ARBDIS = 1 << 6;
        }

        // Section 8.2.3.10.13 DCB Transmit Descriptor Plane Queue Select
        public static uint RTTDQSEL => 0x04904u;

        // Section 8.2.3.10.14 DCB Transmit Descriptor Plane T1 Config
        public static uint RTTDT1C => 0x04908u;

        // Section 8.2.3.8.10 Receive Control Register
        public static uint RXCTRL => 0x03000u;
        public static class RXCTRL_
        {
            public const uint RXEN = 1 << 0;
        }

        // Section 8.2.3.8.6 Receive Descriptor Control
        public static uint RXDCTL(uint n) => n <= 63u ? (0x01028u + 0x40u * n) : (0x0D028u + 0x40u * (n - 64u));
        public static class RXDCTL_
        {
            public const uint ENABLE = 1 << 25;
        }

        // Section 8.2.3.8.9 Receive Packet Buffer Size
        public static uint RXPBSIZE(uint n) => 0x03C00u + 4u * n;

        // Section 8.2.3.12.5 Security Rx Control
        public static uint SECRXCTRL => 0x08D00u;
        public static class SECRXCTRL_
        {
            public const uint RX_DIS = 1 << 1;
        }

        // Section 8.2.3.12.6 Security Rx Status
        public static uint SECRXSTAT => 0x08D04u;
        public static class SECRXSTAT_
        {
            public const uint SECRX_RDY = 1 << 0;
        }

        // Section 8.2.3.8.7 Split Receive Control Registers
        public static uint SRRCTL(uint n) => n <= 63u ? (0x01014u + 0x40u * n) : (0x0D014u + 0x40u * (n - 64u));
        public static class SRRCTL_
        {
            public const uint BSIZEPACKET = 0b0001_1111;
            public const uint DROP_EN = 1 << 28;
        }

        // Section 8.2.3.1.2 Device Status Register
        public static uint STATUS => 0x00008u;
        public static class STATUS_
        {
            public const uint PCIE_MASTER_ENABLE_STATUS = 1 << 19;
        }

        // Section 8.2.3.9.6 Transmit Descriptor Base Address High
        public static uint TDBAH(uint n) => 0x06004u + 0x40u * n;

        // Section 8.2.3.9.5 Transmit Descriptor Base Address Low
        public static uint TDBAL(uint n) => 0x06000u + 0x40u * n;

        // Section 8.2.3.9.7 Transmit Descriptor Length
        public static uint TDLEN(uint n) => 0x06008u + 0x40u * n;

        // Section 8.2.3.9.9 Transmit Descriptor Tail
        public static uint TDT(uint n) => 0x06018u + 0x40u * n;

        // Section 8.2.3.9.11 Tx Descriptor Completion Write Back Address High
        public static uint TDWBAH(uint n) => 0x0603Cu + 0x40u * n;

        // Section 8.2.3.9.11 Tx Descriptor Completion Write Back Address Low
        public static uint TDWBAL(uint n) => 0x06038u + 0x40u * n;

        // Section 8.2.3.9.10 Transmit Descriptor Control
        public static uint TXDCTL(uint n) => 0x06028u + 0x40u * n;
        public static class TXDCTL_
        {
            public const uint PTHRESH = 0b0111_1111;
            public const uint HTHRESH = 0b0111_1111_0000_0000;
            public const uint ENABLE = 1 << 25;
        }

        // Section 8.2.3.9.13 Transmit Packet Buffer Size
        public static uint TXPBSIZE(uint n) => 0x0CC00u + 4u * n;

        // Section 8.2.3.9.16 Tx Packet Buffer Threshold
        public static uint TXPBTHRESH(uint n) => 0x04950u + 4u * n;
        public static class TXPBTHRESH_
        {
            public const uint THRESH = 0b11_1111_1111;
        }
    }

    internal static class DriverConstants
    {
        public const uint RingSize = 256; // to use Array256
        public const uint FlushPeriod = 8;
        public const uint RecyclePeriod = 64;
    }

    internal static class DeviceLimits
    {
        // The following are constants defined by the data sheet.

        // Section 7.1.2.5 L3/L4 5-tuple Filters:
        // 	"There are 128 different 5-tuple filter configuration registers sets"
        public const uint FiveTupleFiltersCount = 128u;

        // Section 7.3.1 Interrupts Registers:
        //	"These registers are extended to 64 bits by an additional set of two registers.
        //	 EICR has an additional two registers EICR(1)... EICR(2) and so on for the EICS, EIMS, EIMC, EIAM and EITR registers."
        public const uint InterruptRegistersCount = 3u;

        // Section 7.10.3.10 Switch Control:
        //	"Multicast Table Array (MTA) - a 4 Kb array that covers all combinations of 12 bits from the MAC destination address."
        public const uint MulticastTableArraySize = 4u * 1024u;

        // Section 7.1.2.2 Queuing in a Virtualized Environment:
        // 	There are 64 pools max (this is also stated in other places)
        public const uint PoolsCount = 64u;

        // Section 7.1.1.1.1 Unicast Filter:
        // 	"The Ethernet MAC address is checked against the 128 host unicast addresses"
        public const uint ReceiveAddressesCount = 128u;

        // Section 1.3 Features Summary:
        // 	"Number of Rx Queues (per port): 128"
        public const uint ReceiveQueuesCount = 128u;

        // 	"Number of Tx Queues (per port): 128"
        public const uint TransmitQueuesCount = 128u;

        // Section 7.1.2 Rx Queues Assignment:
        // 	"Packets are classified into one of several (up to eight) Traffic Classes (TCs)."
        public const uint TrafficClassesCount = 8u;

        // Section 7.10.3.10 Switch Control:
        // 	"Unicast Table Array (PFUTA) - a 4 Kb array that covers all combinations of 12 bits from the MAC destination address"
        public const uint UnicastTableArraySize = 4u * 1024u;
    }
}
