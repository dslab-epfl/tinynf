using System;
using System.Runtime.CompilerServices;
using System.Runtime.InteropServices;
using System.Threading;
using TinyNF.Environment;

namespace TinyNF.Ixgbe
{
    [StructLayout(LayoutKind.Sequential)]
    internal struct Descriptor
    {
        public ulong Addr;
        public ulong Metadata;
    }

    [StructLayout(LayoutKind.Sequential, Size = 64)]
    internal struct TransmitHead
    {
        public uint Value;
    }

    // This struct mimics a safe fixed-size buffer, planned for a future C# version.
    // See https://github.com/dotnet/csharplang/blob/main/proposals/fixed-sized-buffers.md
    // and https://github.com/dotnet/csharplang/issues/1314
    [StructLayout(LayoutKind.Explicit, Size = Size)]
    internal struct PacketData
    {
        public const int Size = 2048;

        public byte this[int index]
        {
            [MethodImpl(MethodImplOptions.AggressiveInlining)]
            get
            {
                // We would like the following, which has bounds checks, because the compiler should be smart enough to remove them:
                // return Volatile.Read(ref MemoryMarshal.Cast<PacketData, byte>(MemoryMarshal.CreateSpan(ref this, 1))[index]);
                // But it currently does not; this depends on https://github.com/dotnet/runtime/pull/62864
                // It was merged but will only be in a later preview
                // TODO: replace this once the code has gotten downstream
                // (instead we bounds-check manually, which the compiler will remove since the index is always known to be <Size)
                if ((uint)index < (uint)Size)
                {
                    return Volatile.Read(ref System.Runtime.CompilerServices.Unsafe.Add(ref System.Runtime.CompilerServices.Unsafe.As<PacketData, byte>(ref this), index));
                }
                else
                {
                    throw new Exception("Out of bounds");
                }
            }
            [MethodImpl(MethodImplOptions.AggressiveInlining)]
            set
            {
                // TODO: same as above
                // Volatile.Write(ref MemoryMarshal.Cast<PacketData, byte>(MemoryMarshal.CreateSpan(ref this, 1))[index], value);
                if ((uint)index < (uint)Size)
                {
                    Volatile.Write(ref System.Runtime.CompilerServices.Unsafe.Add(ref System.Runtime.CompilerServices.Unsafe.As<PacketData, byte>(ref this), index), value);
                }
                else
                {
                    throw new Exception("Out of bounds");
                }
            }
        }
    }

    internal sealed class Device
    {
        public const int RingSize = 256;

        public const ulong RxMetadataDD = 1ul << 32;
        public static ushort RxMetadataLength(ulong metadata) => (ushort)metadata;

        public const ulong TxMetadataEOP = 1ul << 24;
        public const ulong TxMetadataIFCS = 1ul << (24 + 1);
        public const ulong TxMetadataRS = 1ul << (24 + 3);
        public static ulong TxMetadataLength(ulong length) => length;


        private const uint FiveTupleFiltersCount = 128u;
        private const uint InterruptRegistersCount = 3u;
        private const uint MulticastTableArraySize = 4u * 1024u;
        private const uint PoolsCount = 64u;
        private const uint ReceiveAddressesCount = 128u;
        private const uint ReceiveQueuesCount = 128u;
        private const uint TransmitQueuesCount = 128u;
        private const uint TrafficClassesCount = 8u;
        private const uint UnicastTableArraySize = 4u * 1024u;


        private readonly Memory<uint> _buffer;
        private bool _rxEnabled;
        private bool _txEnabled;

        private bool AfterTimeout(IEnvironment environment, TimeSpan span, bool cleared, uint register, uint field)
        {
            environment.Sleep(TimeSpan.FromTicks(span.Ticks % 10));
            for (int n = 0; n < 10; n++)
            {
                if (Regs.IsFieldCleared(_buffer, register, field) != cleared)
                {
                    return false;
                }
                environment.Sleep(span / 10);
            }
            return Regs.IsFieldCleared(_buffer, register, field) == cleared;
        }

        public Device(IEnvironment env, PciAddress pciAddress)
        {
            _rxEnabled = false;
            _txEnabled = false;

            if (IntPtr.Size > 8)
            {
                throw new Exception("Pointers must fit in a ulong");
            }

            uint pciId = env.PciRead(pciAddress, PciRegs.ID);
            if (pciId != ((0x10FBu << 16) | 0x8086u))
            {
                throw new Exception("PCI device is not what was expected");
            }

            if (!PciRegs.IsFieldCleared(env, pciAddress, PciRegs.PMCSR, PciRegs.PMCSR_.POWER_STATE))
            {
                throw new Exception("PCI device not in D0.");
            }

            PciRegs.SetField(env, pciAddress, PciRegs.COMMAND, PciRegs.COMMAND_.BUS_MASTER_ENABLE);
            PciRegs.SetField(env, pciAddress, PciRegs.COMMAND, PciRegs.COMMAND_.MEMORY_ACCESS_ENABLE);
            PciRegs.SetField(env, pciAddress, PciRegs.COMMAND, PciRegs.COMMAND_.INTERRUPT_DISABLE);

            uint pciBar0Low = env.PciRead(pciAddress, PciRegs.BAR0_LOW);
            if ((pciBar0Low & 0b0100) == 0 || (pciBar0Low & 0b0010) != 0)
            {
                throw new Exception("BAR0 is not a 64-bit BAR");
            }
            uint pciBar0High = env.PciRead(pciAddress, PciRegs.BAR0_HIGH);

            ulong devPhysAddr = (((ulong)pciBar0High) << 32) | (pciBar0Low & ~(ulong)0b1111);
            _buffer = env.MapPhysicalMemory<uint>(devPhysAddr, 128 * 1024 / sizeof(uint));

            // Console.WriteLine("Device {0:X}:{1:X}.{2:X} with BAR {3} mapped", pciAddress.Bus, pciAddress.Device, pciAddress.Function, devPhysAddr);

            for (byte queue = 0; queue < ReceiveQueuesCount; queue++)
            {
                Regs.ClearField(_buffer, Regs.RXDCTL(queue), Regs.RXDCTL_.ENABLE);
                if (AfterTimeout(env, TimeSpan.FromSeconds(1), cleared: false, Regs.RXDCTL(queue), Regs.RXDCTL_.ENABLE))
                {
                    throw new Exception("RXDCTL.ENABLE did not clear, cannot disable receive to reset");
                }
                env.Sleep(TimeSpan.FromMilliseconds(0.1));
            }

            Regs.SetField(_buffer, Regs.CTRL, Regs.CTRL_.MASTER_DISABLE);
            if (AfterTimeout(env, TimeSpan.FromSeconds(1), cleared: false, Regs.STATUS, Regs.STATUS_.PCIE_MASTER_ENABLE_STATUS))
            {
                if (!PciRegs.IsFieldCleared(env, pciAddress, PciRegs.DEVICESTATUS, PciRegs.DEVICESTATUS_.TRANSACTIONPENDING))
                {
                    throw new Exception("DEVICESTATUS.TRANSACTIONPENDING did not clear, cannot perform master disable to reset");
                }

                Regs.SetField(_buffer, Regs.HLREG0, Regs.HLREG0_.LPBK);
                Regs.ClearField(_buffer, Regs.RXCTRL, Regs.RXCTRL_.RXEN);

                Regs.SetField(_buffer, Regs.GCREXT, Regs.GCREXT_.BUFFERS_CLEAR_FUNC);
                env.Sleep(TimeSpan.FromMilliseconds(0.02));

                Regs.ClearField(_buffer, Regs.HLREG0, Regs.HLREG0_.LPBK);
                Regs.ClearField(_buffer, Regs.GCREXT, Regs.GCREXT_.BUFFERS_CLEAR_FUNC);

                Regs.SetField(_buffer, Regs.CTRL, Regs.CTRL_.RST);
                env.Sleep(TimeSpan.FromMilliseconds(0.002));
            }

            Regs.SetField(_buffer, Regs.CTRL, Regs.CTRL_.RST);

            env.Sleep(TimeSpan.FromMilliseconds(1));
            env.Sleep(TimeSpan.FromMilliseconds(10));

            Regs.Write(_buffer, Regs.EIMC(0), 0x7FFFFFFFu);
            for (byte n = 1; n < InterruptRegistersCount; n++)
            {
                Regs.Write(_buffer, Regs.EIMC(n), 0xFFFFFFFFu);
            }

            Regs.WriteField(_buffer, Regs.FCRTH(0), Regs.FCRTH_.RTH, (512 * 1024 - 0x6000) / 32);

            if (AfterTimeout(env, TimeSpan.FromSeconds(1), cleared: true, Regs.EEC, Regs.EEC_.AUTO_RD))
            {
                throw new Exception("EEPROM auto read timed out");
            }

            if (Regs.IsFieldCleared(_buffer, Regs.EEC, Regs.EEC_.EE_PRES) || !Regs.IsFieldCleared(_buffer, Regs.FWSM, Regs.FWSM_.EXT_ERR_IND))
            {
                throw new Exception("EEPROM not present or invalid");
            }

            if (AfterTimeout(env, TimeSpan.FromSeconds(1), cleared: true, Regs.RDRXCTL, Regs.RDRXCTL_.DMAIDONE))
            {
                throw new Exception("DMA init timed out");
            }

            for (uint n = 0; n < UnicastTableArraySize / 32; n++)
            {
                Regs.Clear(_buffer, Regs.PFUTA(n));
            }

            for (byte n = 0; n < PoolsCount; n++)
            {
                Regs.Clear(_buffer, Regs.PFVLVF(n));
            }

            Regs.Write(_buffer, Regs.MPSAR(0), 1);
            for (ushort n = 1; n < ReceiveAddressesCount * 2; n++)
            {
                Regs.Clear(_buffer, Regs.MPSAR(n));
            }

            for (byte n = 0; n < PoolsCount * 2; n++)
            {
                Regs.Clear(_buffer, Regs.PFVLVFB(n));
            }

            for (uint n = 0; n < MulticastTableArraySize / 32; n++)
            {
                Regs.Clear(_buffer, Regs.MTA(n));
            }

            for (byte n = 0; n < FiveTupleFiltersCount; n++)
            {
                Regs.ClearField(_buffer, Regs.FTQF(n), Regs.FTQF_.QUEUE_ENABLE);
            }

            Regs.SetField(_buffer, Regs.RDRXCTL, Regs.RDRXCTL_.CRC_STRIP);

            Regs.ClearField(_buffer, Regs.RDRXCTL, Regs.RDRXCTL_.RSCFRSTSIZE);

            Regs.SetField(_buffer, Regs.RDRXCTL, Regs.RDRXCTL_.RSCACKC);

            Regs.SetField(_buffer, Regs.RDRXCTL, Regs.RDRXCTL_.FCOE_WRFIX);

            for (byte n = 1; n < TrafficClassesCount; n++)
            {
                Regs.Clear(_buffer, Regs.RXPBSIZE(n));
            }

            Regs.SetField(_buffer, Regs.MFLCN, Regs.MFLCN_.RFCE);

            Regs.WriteField(_buffer, Regs.FCCFG, Regs.FCCFG_.TFCE, 1);

            for (byte n = 0; n < TransmitQueuesCount; n++)
            {
                Regs.Write(_buffer, Regs.RTTDQSEL, n);
                Regs.Clear(_buffer, Regs.RTTDT1C);
            }

            Regs.SetField(_buffer, Regs.RTTDCS, Regs.RTTDCS_.ARBDIS);

            for (byte n = 1; n < TrafficClassesCount; n++)
            {
                Regs.Clear(_buffer, Regs.TXPBSIZE(n));
            }

            Regs.WriteField(_buffer, Regs.TXPBTHRESH(0), Regs.TXPBTHRESH_.THRESH, 0xA0u - (PacketData.Size / 1024u));

            Regs.WriteField(_buffer, Regs.DTXMXSZRQ, Regs.DTXMXSZRQ_.MAX_BYTES_NUM_REQ, 0xFFF);

            Regs.ClearField(_buffer, Regs.RTTDCS, Regs.RTTDCS_.ARBDIS);
        }

        public void SetPromiscuous()
        {
            if (_rxEnabled)
            {
                Regs.ClearField(_buffer, Regs.RXCTRL, Regs.RXCTRL_.RXEN);
            }

            Regs.SetField(_buffer, Regs.FCTRL, Regs.FCTRL_.UPE);

            Regs.SetField(_buffer, Regs.FCTRL, Regs.FCTRL_.MPE);

            if (_rxEnabled)
            {
                Regs.SetField(_buffer, Regs.RXCTRL, Regs.RXCTRL_.RXEN);
            }
        }

        internal Memory<uint> SetInput(IEnvironment env, Span<Descriptor> ring)
        {
            uint queueIndex = 0;

            if (!Regs.IsFieldCleared(_buffer, Regs.RXDCTL(queueIndex), Regs.RXDCTL_.ENABLE))
            {
                throw new Exception("Receive queue is already in use");
            }

            nuint ringPhysAddr = env.GetPhysicalAddress(ref ring.GetPinnableReference());
            Regs.Write(_buffer, Regs.RDBAH(queueIndex), (uint)(ringPhysAddr >> 32));
            Regs.Write(_buffer, Regs.RDBAL(queueIndex), (uint)ringPhysAddr);

            Regs.Write(_buffer, Regs.RDLEN(queueIndex), RingSize * 16u);

            Regs.WriteField(_buffer, Regs.SRRCTL(queueIndex), Regs.SRRCTL_.BSIZEPACKET, PacketData.Size / 1024u);

            Regs.SetField(_buffer, Regs.SRRCTL(queueIndex), Regs.SRRCTL_.DROP_EN);

            Regs.SetField(_buffer, Regs.RXDCTL(queueIndex), Regs.RXDCTL_.ENABLE);
            if (AfterTimeout(env, TimeSpan.FromSeconds(1), cleared: true, Regs.RXDCTL(queueIndex), Regs.RXDCTL_.ENABLE))
            {
                throw new Exception("RXDCTL.ENABLE did not set, cannot enable queue");
            }

            Regs.Write(_buffer, Regs.RDT(queueIndex), RingSize - 1u);

            if (!_rxEnabled)
            {
                Regs.SetField(_buffer, Regs.SECRXCTRL, Regs.SECRXCTRL_.RX_DIS);

                if (AfterTimeout(env, TimeSpan.FromSeconds(1), cleared: true, Regs.SECRXSTAT, Regs.SECRXSTAT_.SECRX_RDY))
                {
                    throw new Exception("SECRXSTAT.SECRXRDY timed out, cannot start device");
                }

                Regs.SetField(_buffer, Regs.RXCTRL, Regs.RXCTRL_.RXEN);

                Regs.ClearField(_buffer, Regs.SECRXCTRL, Regs.SECRXCTRL_.RX_DIS);

                Regs.SetField(_buffer, Regs.CTRLEXT, Regs.CTRLEXT_.NSDIS);

                _rxEnabled = true;
            }

            Regs.ClearField(_buffer, Regs.DCARXCTRL(queueIndex), Regs.DCARXCTRL_.UNKNOWN);

            return _buffer.Slice((int)Regs.RDT(queueIndex), 1);
        }

        internal Memory<uint> AddOutput(IEnvironment env, Span<Descriptor> ring, ref TransmitHead transmitHead)
        {
            uint queueIndex = 0;
            for (; queueIndex < TransmitQueuesCount; queueIndex++)
            {
                if (Regs.IsFieldCleared(_buffer, Regs.TXDCTL(queueIndex), Regs.TXDCTL_.ENABLE))
                {
                    break;
                }
            }
            if (queueIndex == TransmitQueuesCount)
            {
                throw new Exception("No available transmit queues");
            }


            nuint ringPhysAddr = env.GetPhysicalAddress(ref ring.GetPinnableReference());
            Regs.Write(_buffer, Regs.TDBAH(queueIndex), (uint)(ringPhysAddr >> 32));
            Regs.Write(_buffer, Regs.TDBAL(queueIndex), (uint)ringPhysAddr);

            Regs.Write(_buffer, Regs.TDLEN(queueIndex), RingSize * 16u);

            Regs.WriteField(_buffer, Regs.TXDCTL(queueIndex), Regs.TXDCTL_.PTHRESH, 60);
            Regs.WriteField(_buffer, Regs.TXDCTL(queueIndex), Regs.TXDCTL_.HTHRESH, 4);

            nuint headPhysAddr = env.GetPhysicalAddress(ref transmitHead.Value);

            if (headPhysAddr % 16u != 0)
            {
                throw new Exception("Transmit head's physical address is not aligned properly");
            }

            Regs.Write(_buffer, Regs.TDWBAH(queueIndex), (uint)(headPhysAddr >> 32));
            Regs.Write(_buffer, Regs.TDWBAL(queueIndex), (uint)headPhysAddr | 1u);

            Regs.ClearField(_buffer, Regs.DCATXCTRL(queueIndex), Regs.DCATXCTRL_.TX_DESC_WB_RO_EN);

            if (!_txEnabled)
            {
                Regs.SetField(_buffer, Regs.DMATXCTL, Regs.DMATXCTL_.TE);
                _txEnabled = true;
            }

            Regs.SetField(_buffer, Regs.TXDCTL(queueIndex), Regs.TXDCTL_.ENABLE);
            if (AfterTimeout(env, TimeSpan.FromSeconds(1), cleared: true, Regs.TXDCTL(queueIndex), Regs.TXDCTL_.ENABLE))
            {
                throw new Exception("TXDCTL.ENABLE did not set, cannot enable queue");
            }


            return _buffer.Slice((int)Regs.TDT(queueIndex), 1);
        }
    }
}
