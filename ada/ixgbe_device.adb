with Interfaces; use Interfaces;
with System.Storage_Elements;
with Text_IO;
with GNAT.OS_Lib;

with Ixgbe_Pci_Regs;

package body Ixgbe_Device is
  package Pci_Regs renames Ixgbe_Pci_Regs;

  function Init_Device(Addr: in Pci_Address) return Dev is
  begin
    if System.Storage_Elements.Integer_Address'Size > 64 then
      Text_IO.Put_Line("Pointers must fit in 64 bits");
      GNAT.OS_Lib.OS_Abort;
    end if;

    declare
      Pci_Id: Interfaces.Unsigned_32; -- !!! fix
    begin
      Pci_Id := Environment.Pci_Read(Addr, Pci_Regs.ID);
      if Pci_Id /= 16#10FB8086# then
        Text_IO.Put_Line("PCI device is not what was expected");
        GNAT.OS_Lib.OS_Abort;
      end if;
    end;

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

            //            Console.WriteLine("Device {0:X}:{1:X}.{2:X} with BAR {3} mapped", pciAddress.Bus, pciAddress.Device, pciAddress.Function, devPhysAddr);


            for (byte queue = 0; queue < DeviceLimits.ReceiveQueuesCount; queue++)
            {
                Regs.ClearField(_buffer, Regs.RXDCTL(queue), Regs.RXDCTL_.ENABLE);
                IfAfterTimeout(env, TimeSpan.FromSeconds(1), () => !Regs.IsFieldCleared(_buffer, Regs.RXDCTL(queue), Regs.RXDCTL_.ENABLE), () =>
                {
                    throw new Exception("RXDCTL.ENABLE did not clear, cannot disable receive to reset");
                });
                env.Sleep(TimeSpan.FromMilliseconds(0.1));
            }

            Regs.SetField(_buffer, Regs.CTRL, Regs.CTRL_.MASTER_DISABLE);
            IfAfterTimeout(env, TimeSpan.FromSeconds(1), () => !Regs.IsFieldCleared(_buffer, Regs.STATUS, Regs.STATUS_.PCIE_MASTER_ENABLE_STATUS), () =>
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
            });

            Regs.SetField(_buffer, Regs.CTRL, Regs.CTRL_.RST);

            env.Sleep(TimeSpan.FromMilliseconds(1));
            env.Sleep(TimeSpan.FromMilliseconds(10));

            Regs.Write(_buffer, Regs.EIMC(0), 0x7FFFFFFFu);
            for (byte n = 1; n < DeviceLimits.InterruptRegistersCount; n++)
            {
                Regs.Write(_buffer, Regs.EIMC(n), 0xFFFFFFFFu);
            }

            Regs.WriteField(_buffer, Regs.FCRTH(0), Regs.FCRTH_.RTH, (512 * 1024 - 0x6000) / 32);

            IfAfterTimeout(env, TimeSpan.FromSeconds(1), () => Regs.IsFieldCleared(_buffer, Regs.EEC, Regs.EEC_.AUTO_RD), () =>
            {
                throw new Exception("EEPROM auto read timed out");
            });

            if (Regs.IsFieldCleared(_buffer, Regs.EEC, Regs.EEC_.EE_PRES) || !Regs.IsFieldCleared(_buffer, Regs.FWSM, Regs.FWSM_.EXT_ERR_IND))
            {
                throw new Exception("EEPROM not present or invalid");
            }

            IfAfterTimeout(env, TimeSpan.FromSeconds(1), () => Regs.IsFieldCleared(_buffer, Regs.RDRXCTL, Regs.RDRXCTL_.DMAIDONE), () =>
            {
                throw new Exception("DMA init timed out");
            });

            for (uint n = 0; n < DeviceLimits.UnicastTableArraySize / 32; n++)
            {
                Regs.Clear(_buffer, Regs.PFUTA(n));
            }

            for (byte n = 0; n < DeviceLimits.PoolsCount; n++)
            {
                Regs.Clear(_buffer, Regs.PFVLVF(n));
            }

            Regs.Write(_buffer, Regs.MPSAR(0), 1);
            for (ushort n = 1; n < DeviceLimits.ReceiveAddressesCount * 2; n++)
            {
                Regs.Clear(_buffer, Regs.MPSAR(n));
            }

            for (byte n = 0; n < DeviceLimits.PoolsCount * 2; n++)
            {
                Regs.Clear(_buffer, Regs.PFVLVFB(n));
            }

            for (uint n = 0; n < DeviceLimits.MulticastTableArraySize / 32; n++)
            {
                Regs.Clear(_buffer, Regs.MTA(n));
            }

            for (byte n = 0; n < DeviceLimits.FiveTupleFiltersCount; n++)
            {
                Regs.ClearField(_buffer, Regs.FTQF(n), Regs.FTQF_.QUEUE_ENABLE);
            }

            Regs.SetField(_buffer, Regs.RDRXCTL, Regs.RDRXCTL_.CRC_STRIP);

            Regs.ClearField(_buffer, Regs.RDRXCTL, Regs.RDRXCTL_.RSCFRSTSIZE);

            Regs.SetField(_buffer, Regs.RDRXCTL, Regs.RDRXCTL_.RSCACKC);

            Regs.SetField(_buffer, Regs.RDRXCTL, Regs.RDRXCTL_.FCOE_WRFIX);

            for (byte n = 1; n < DeviceLimits.TrafficClassesCount; n++)
            {
                Regs.Clear(_buffer, Regs.RXPBSIZE(n));
            }

            Regs.SetField(_buffer, Regs.MFLCN, Regs.MFLCN_.RFCE);

            Regs.WriteField(_buffer, Regs.FCCFG, Regs.FCCFG_.TFCE, 1);

            for (byte n = 0; n < DeviceLimits.TransmitQueuesCount; n++)
            {
                Regs.Write(_buffer, Regs.RTTDQSEL, n);
                Regs.Clear(_buffer, Regs.RTTDT1C);
            }

            Regs.SetField(_buffer, Regs.RTTDCS, Regs.RTTDCS_.ARBDIS);

            for (byte n = 1; n < DeviceLimits.TrafficClassesCount; n++)
            {
                Regs.Clear(_buffer, Regs.TXPBSIZE(n));
            }

            Regs.WriteField(_buffer, Regs.TXPBTHRESH(0), Regs.TXPBTHRESH_.THRESH, 0xA0u - (PacketData.Size / 1024u));

            Regs.WriteField(_buffer, Regs.DTXMXSZRQ, Regs.DTXMXSZRQ_.MAX_BYTES_NUM_REQ, 0xFFF);

            Regs.ClearField(_buffer, Regs.RTTDCS, Regs.RTTDCS_.ARBDIS);
        }
  end;
end Ixgbe_Device;
