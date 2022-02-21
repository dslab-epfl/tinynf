using System;
using System.Numerics;
using System.Threading;
using TinyNF.Environment;

namespace TinyNF.Ixgbe
{
    internal static class Regs
    {
        public const uint CTRL = 0x00000u / 4u;
        public static class CTRL_
        {
            public const uint MASTER_DISABLE = 1 << 2;
            public const uint RST = 1 << 26;
        }

        public const uint CTRLEXT = 0x00018u / 4u;
        public static class CTRLEXT_
        {
            public const uint NSDIS = 1 << 16;
        }

        public static uint DCARXCTRL(uint n) => n <= 63u ? (0x0100Cu / 4u + 0x10u * n) : (0x0D00Cu / 4u + 0x10u * (n - 64u));
        public static class DCARXCTRL_
        {
            public const uint UNKNOWN = 1 << 12;
        }

        public static uint DCATXCTRL(uint n) => 0x0600Cu / 4u + 0x10u * n;
        public static class DCATXCTRL_
        {
            public const uint TX_DESC_WB_RO_EN = 1 << 11;
        }

        public const uint DMATXCTL = 0x04A80u / 4u;
        public static class DMATXCTL_
        {
            public const uint TE = 1 << 0;
        }

        public const uint DTXMXSZRQ = 0x08100u / 4u;
        public static class DTXMXSZRQ_
        {
            public const uint MAX_BYTES_NUM_REQ = 0b0111_1111_1111;
        }

        public const uint EEC = 0x10010u / 4u;
        public static class EEC_
        {
            public const uint EE_PRES = 1 << 8;
            public const uint AUTO_RD = 1 << 9;
        }

        public static uint EIMC(uint n) => n == 0 ? (0x00888u / 4u) : (0x00AB0u / 4u + (n - 1u));

        public const uint FCCFG = 0x03D00u / 4u;
        public static class FCCFG_
        {
            public const uint TFCE = 0b0001_1000;
        }

        public static uint FCRTH(uint n) => 0x03260u / 4u + n;
        public static class FCRTH_
        {
            public const uint RTH = 0b0111_1111_1111_1110_0000;
        }

        public const uint FCTRL = 0x05080u / 4u;
        public static class FCTRL_
        {
            public const uint MPE = 1 << 8;
            public const uint UPE = 1 << 9;
        }

        public static uint FTQF(uint n) => 0x0E600u / 4u + n;
        public static class FTQF_
        {
            public const uint QUEUE_ENABLE = 1u << 31;
        }

        public const uint FWSM = 0x10148u / 4u;
        public static class FWSM_
        {
            public const uint EXT_ERR_IND = 0b0001_1111_1000_0000_0000_0000_0000;
        }

        public const uint GCREXT = 0x11050u / 4u;
        public static class GCREXT_
        {
            public const uint BUFFERS_CLEAR_FUNC = 1 << 30;
        }

        public const uint HLREG0 = 0x04240u / 4u;
        public static class HLREG0_
        {
            public const uint LPBK = 1 << 15;
        }

        public const uint MFLCN = 0x04294u / 4u;
        public static class MFLCN_
        {
            public const uint RFCE = 1 << 3;
        }

        public static uint MPSAR(uint n) => 0x0A600u / 4u + n;

        public static uint MTA(uint n) => 0x05200u / 4u + n;

        public static uint PFUTA(uint n) => 0x0F400u / 4u + n;

        public static uint PFVLVF(uint n) => 0x0F100u / 4u + n;

        public static uint PFVLVFB(uint n) => 0x0F200u / 4u + n;

        public static uint RDBAH(uint n) => n <= 63u ? (0x01004u / 4u + 0x10u * n) : (0x0D004u / 4u + 0x10u * (n - 64u));

        public static uint RDBAL(uint n) => n <= 63u ? (0x01000u / 4u + 0x10u * n) : (0x0D000u / 4u + 0x10u * (n - 64u));

        public static uint RDLEN(uint n) => n <= 63u ? (0x01008u / 4u + 0x10u * n) : (0x0D008u / 4u + 0x10u * (n - 64u));

        public const uint RDRXCTL = 0x02F00u / 4u;
        public static class RDRXCTL_
        {
            public const uint CRC_STRIP = 1 << 1;
            public const uint DMAIDONE = 1 << 3;
            public const uint RSCFRSTSIZE = 0b0011_1110_0000_0000_0000_0000;
            public const uint RSCACKC = 1 << 25;
            public const uint FCOE_WRFIX = 1 << 26;
        }

        public static uint RDT(uint n) => n <= 63u ? (0x01018u / 4u + 0x10u * n) : (0x0D018u / 4u + 0x10u * (n - 64u));

        public const uint RTTDCS = 0x04900u / 4u;
        public static class RTTDCS_
        {
            public const uint ARBDIS = 1 << 6;
        }

        public const uint RTTDQSEL = 0x04904u / 4u;

        public const uint RTTDT1C = 0x04908u / 4u;

        public const uint RXCTRL = 0x03000u / 4u;
        public static class RXCTRL_
        {
            public const uint RXEN = 1 << 0;
        }

        public static uint RXDCTL(uint n) => n <= 63u ? (0x01028u / 4u + 0x10u * n) : (0x0D028u / 4u + 0x10u * (n - 64u));
        public static class RXDCTL_
        {
            public const uint ENABLE = 1 << 25;
        }

        public static uint RXPBSIZE(uint n) => 0x03C00u / 4u + n;

        public const uint SECRXCTRL = 0x08D00u / 4u;
        public static class SECRXCTRL_
        {
            public const uint RX_DIS = 1 << 1;
        }

        public const uint SECRXSTAT = 0x08D04u / 4u;
        public static class SECRXSTAT_
        {
            public const uint SECRX_RDY = 1 << 0;
        }

        public static uint SRRCTL(uint n) => n <= 63u ? (0x01014u / 4u + 0x10u * n) : (0x0D014u / 4u + 0x10u * (n - 64u));
        public static class SRRCTL_
        {
            public const uint BSIZEPACKET = 0b0001_1111;
            public const uint DROP_EN = 1 << 28;
        }

        public const uint STATUS = 0x00008u / 4u;
        public static class STATUS_
        {
            public const uint PCIE_MASTER_ENABLE_STATUS = 1 << 19;
        }

        public static uint TDBAH(uint n) => 0x06004u / 4u + 0x10u * n;

        public static uint TDBAL(uint n) => 0x06000u / 4u + 0x10u * n;

        public static uint TDLEN(uint n) => 0x06008u / 4u + 0x10u * n;

        public static uint TDT(uint n) => 0x06018u / 4u + 0x10u * n;

        public static uint TDWBAH(uint n) => 0x0603Cu / 4u + 0x10u * n;

        public static uint TDWBAL(uint n) => 0x06038u / 4u + 0x10u * n;

        public static uint TXDCTL(uint n) => 0x06028u / 4u + 0x10u * n;
        public static class TXDCTL_
        {
            public const uint PTHRESH = 0b0111_1111;
            public const uint HTHRESH = 0b0111_1111_0000_0000;
            public const uint ENABLE = 1 << 25;
        }

        public static uint TXPBSIZE(uint n) => 0x0CC00u / 4u + n;

        public static uint TXPBTHRESH(uint n) => 0x04950u / 4u + n;
        public static class TXPBTHRESH_
        {
            public const uint THRESH = 0b11_1111_1111;
        }


        public static uint Read(Memory<uint> buffer, uint reg)
        {
            return Endianness.FromLittle(Volatile.Read(ref buffer.Span[(int)reg]));
        }

        public static uint ReadField(Memory<uint> buffer, uint reg, uint field)
        {
            uint value = Read(buffer, reg);
            int shift = BitOperations.TrailingZeroCount(field);
            return (value & field) >> shift;
        }

        public static void Write(Memory<uint> buffer, uint reg, uint value)
        {
            Volatile.Write(ref buffer.Span[(int)reg], Endianness.ToLittle(value));
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
    }
}
