with Interfaces; use Interfaces;
with System.Storage_Elements;
with Text_IO;
with GNAT.OS_Lib;

with Ixgbe_Pci_Regs;
with Ixgbe_Regs;

package body Ixgbe_Device is
  package Pci_Regs renames Ixgbe_Pci_Regs;
  package Regs renames Ixgbe_Regs;

  function After_Timeout(Timeout: Duration; Cleared: Boolean; Buffer: access Device_Buffer; Reg: in Interfaces.Unsigned_32; Field: in Interfaces.Unsigned_32) return Boolean is
  begin
    delay 0.001; -- no point in doing a % here like in other langs since our timeout is a float
    for I in 1 .. 10 loop
      if Cleared /= Regs.Is_Field_Cleared(Buffer, Reg, Field) then
        return false;
      end if;
      delay Timeout / 10.0;
    end loop;
    return Cleared = Regs.Is_Field_Cleared(Buffer, Reg, Field);
  end;

  function Init_Device(Addr: in Pci_Address) return Device is
    Buffer: access Device_Buffer;
    Pci_Bar0_Low: Interfaces.Unsigned_32;
    Pci_Bar0_High: Interfaces.Unsigned_32;
    Device_Phys_Addr: System.Storage_Elements.Integer_Address;
    function Map_Buffer is new Environment.Map_Physical_Memory(T => VolatileUInt32, R => Device_Buffer_Range, T_Array => Device_Buffer);
  begin
    if System.Storage_Elements.Integer_Address'Size > 64 then
      Text_IO.Put_Line("Pointers must fit in 64 bits");
      GNAT.OS_Lib.OS_Abort;
    end if;

    declare
      Pci_Id: Interfaces.Unsigned_32;
    begin
      Pci_Id := Environment.Pci_Read(Addr, Pci_Regs.ID);
      if Pci_Id /= 16#10FB8086# then
        Text_IO.Put_Line("PCI device is not what was expected");
        GNAT.OS_Lib.OS_Abort;
      end if;
    end;

    if not Pci_Regs.Is_Field_Cleared(Addr, Pci_Regs.PMCSR, Pci_Regs.PMCSR_POWER_STATE) then
      Text_IO.Put_Line("PCI device not in D0.");
      GNAT.OS_Lib.OS_Abort;
    end if;

    Pci_Regs.Set_Field(Addr, Pci_Regs.COMMAND, Pci_Regs.COMMAND_BUS_MASTER_ENABLE);
    Pci_Regs.Set_Field(Addr, Pci_Regs.COMMAND, Pci_Regs.COMMAND_MEMORY_ACCESS_ENABLE);
    Pci_Regs.Set_Field(Addr, Pci_Regs.COMMAND, Pci_Regs.COMMAND_INTERRUPT_DISABLE);

    Pci_Bar0_Low := Environment.Pci_Read(Addr, Pci_Regs.BAR0_LOW);
    if (Pci_Bar0_Low and 2#0100#) = 0 or (Pci_Bar0_Low and 2#0010#) /= 0 then
      Text_IO.Put_Line("BAR0 is not a 64-bit BAR");
      GNAT.OS_Lib.OS_Abort;
    end if;
    Pci_Bar0_High := Environment.Pci_Read(Addr, Pci_Regs.BAR0_HIGH);
    Device_Phys_Addr := System.Storage_Elements.Integer_Address(Shift_Left(Interfaces.Unsigned_64(Pci_Bar0_High), 32) or Interfaces.Unsigned_64(Pci_Bar0_Low and not 2#1111#));
    Buffer := Map_Buffer(Device_Phys_Addr);

    for Queue in 0 .. Receive_Queues_Count - 1 loop
      Regs.Clear_Field(Buffer, Regs.RXDCTL(Queue), Regs.RXDCTL_ENABLE);
      if After_Timeout(1.0, false, Buffer, Regs.RXDCTL(Queue), Regs.RXDCTL_ENABLE) then
        Text_IO.Put_Line("RXDCTL.ENABLE did not clear, cannot disable receive to reset");
        GNAT.OS_Lib.OS_Abort;
      end if;
      delay 0.0001;
    end loop;

    Regs.Set_Field(Buffer, Regs.CTRL, Regs.CTRL_MASTER_DISABLE);
    if After_Timeout(1.0, false, Buffer, Regs.STATUS, Regs.STATUS_PCIE_MASTER_ENABLE_STATUS) then
      if not Pci_Regs.Is_Field_Cleared(Addr, Pci_Regs.DEVICESTATUS, Pci_Regs.DEVICESTATUS_TRANSACTIONPENDING) then
        Text_IO.Put_Line("DEVICESTATUS.TRANSACTIONPENDING did not clear, cannot perform master disable to reset");
        GNAT.OS_Lib.OS_Abort;
      end if;

      Regs.Set_Field(Buffer, Regs.HLREG0, Regs.HLREG0_LPBK);
      Regs.Clear_Field(Buffer, Regs.RXCTRL, Regs.RXCTRL_RXEN);

      Regs.Set_Field(Buffer, Regs.GCREXT, Regs.GCREXT_BUFFERS_CLEAR_FUNC);
      delay 0.00002;

      Regs.Clear_Field(Buffer, Regs.HLREG0, Regs.HLREG0_LPBK);
      Regs.Clear_Field(Buffer, Regs.GCREXT, Regs.GCREXT_BUFFERS_CLEAR_FUNC);

      Regs.Set_Field(Buffer, Regs.CTRL, Regs.CTRL_RST);
      delay 0.00002;
    end if;

    Regs.Set_Field(Buffer, Regs.CTRL, Regs.CTRL_RST);

    delay 0.001;
    delay 0.01;

    Regs.Write(Buffer, Regs.EIMC(0), 16#7FFFFFFF#);
    for N in 1 .. Interrupt_Registers_Count - 1 loop
      Regs.Write(Buffer, Regs.EIMC(N), 16#FFFFFFFF#);
    end loop;

    Regs.Write_Field(Buffer, Regs.FCRTH(0), Regs.FCRTH_RTH, (512 * 1024 - 16#6000#) / 32);

    if After_Timeout(1.0, true, Buffer, Regs.EEC, Regs.EEC_AUTO_RD) then
      Text_IO.Put_Line("EEPROM auto read timed out");
      GNAT.OS_Lib.OS_Abort;
    end if;

    if Regs.Is_Field_Cleared(Buffer, Regs.EEC, Regs.EEC_EE_PRES) or not Regs.Is_Field_Cleared(Buffer, Regs.FWSM, Regs.FWSM_EXT_ERR_IND) then
      Text_IO.Put_Line("EEPROM not present or invalid");
      GNAT.OS_Lib.OS_Abort;
    end if;

    if After_Timeout(1.0, true, Buffer, Regs.RDRXCTL, Regs.RDRXCTL_DMAIDONE) then
      Text_IO.Put_Line("DMA init timed out");
      GNAT.OS_Lib.OS_Abort;
    end if;

    for N in 0 .. Unicast_Table_Array_Size / 32 - 1 loop
      Regs.Clear(Buffer, Regs.PFUTA(N));
    end loop;

    for N in 0 .. Pools_Count - 1 loop
      Regs.Clear(Buffer, Regs.PFVLVF(N));
    end loop;

    Regs.Write(Buffer, Regs.MPSAR(0), 1);
    for N in 1 .. Receive_Addresses_Count * 2 - 1 loop
      Regs.Clear(Buffer, Regs.MPSAR(N));
    end loop;

    for N in 0 .. Pools_Count * 2 - 1 loop
      Regs.Clear(Buffer, Regs.PFVLVFB(N));
    end loop;

    for N in 0 .. Multicast_Table_Array_Size / 32 - 1 loop
      Regs.Clear(Buffer, Regs.MTA(N));
    end loop;

    for N in 0 .. FiveTuple_Filters_Count - 1 loop
      Regs.Clear_Field(Buffer, Regs.FTQF(N), Regs.FTQF_QUEUE_ENABLE);
    end loop;

    Regs.Set_Field(Buffer, Regs.RDRXCTL, Regs.RDRXCTL_CRC_STRIP);

    Regs.Clear_Field(Buffer, Regs.RDRXCTL, Regs.RDRXCTL_RSCFRSTSIZE);

    Regs.Set_Field(Buffer, Regs.RDRXCTL, Regs.RDRXCTL_RSCACKC);

    Regs.Set_Field(Buffer, Regs.RDRXCTL, Regs.RDRXCTL_FCOE_WRFIX);

    for N in 1 .. Traffic_Classes_Count - 1 loop
      Regs.Clear(Buffer, Regs.RXPBSIZE(N));
    end loop;

    Regs.Set_Field(Buffer, Regs.MFLCN, Regs.MFLCN_RFCE);

    Regs.Write_Field(Buffer, Regs.FCCFG, Regs.FCCFG_TFCE, 1);

    for N in 0 .. Transmit_Queues_Count - 1 loop
      Regs.Write(Buffer, Regs.RTTDQSEL, Interfaces.Unsigned_32(N));
      Regs.Clear(Buffer, Regs.RTTDT1C);
    end loop;

    Regs.Set_Field(Buffer, Regs.RTTDCS, Regs.RTTDCS_ARBDIS);

    for N in 1 .. Traffic_Classes_Count - 1 loop
      Regs.Clear(Buffer, Regs.TXPBSIZE(N));
    end loop;

    Regs.Write_Field(Buffer, Regs.TXPBTHRESH(0), Regs.TXPBTHRESH_THRESH, 16#A0# - (Packet_Buffer_Size / 1024));

    Regs.Write_Field(Buffer, Regs.DTXMXSZRQ, Regs.DTXMXSZRQ_MAX_BYTES_NUM_REQ, 16#FFF#);

    Regs.Clear_Field(Buffer, Regs.RTTDCS, Regs.RTTDCS_ARBDIS);

    return (Buffer => Buffer.all'Unchecked_Access, RX_Enabled => False, TX_Enabled => False); -- no idea why this .all'unchecked is necessary, but it raises an access error otherwise
  end;

  procedure Set_Promiscuous(Dev: in out Device) is
  begin
    if Dev.RX_Enabled then
      Regs.Clear_Field(Dev.Buffer, Regs.RXCTRL, Regs.RXCTRL_RXEN);
    end if;

    Regs.Set_Field(Dev.Buffer, Regs.FCTRL, Regs.FCTRL_UPE);

    Regs.Set_Field(Dev.Buffer, Regs.FCTRL, Regs.FCTRL_MPE);

    if Dev.RX_Enabled then
      Regs.Set_Field(Dev.Buffer, Regs.RXCTRL, Regs.RXCTRL_RXEN);
    end if;
  end;

  function Set_Input(Dev: not null access Device; Ring: not null access Descriptor_Ring) return Register_Access is
    Queue_Index: constant Integer := 0;
    Ring_Phys_Addr: Interfaces.Unsigned_64;
    function Get_Ring_Addr is new Environment.Get_Physical_Address(T => Descriptor);
  begin
    if not Regs.Is_Field_Cleared(Dev.Buffer, Regs.RXDCTL(Queue_Index), Regs.RXDCTL_ENABLE) then
      Text_IO.Put_Line("Receive queue is already in use");
      GNAT.OS_Lib.OS_Abort;
    end if;

    Ring_Phys_Addr := Interfaces.Unsigned_64(Get_Ring_Addr(Ring(0)'Access));
    Regs.Write(Dev.Buffer, Regs.RDBAH(Queue_Index), Interfaces.Unsigned_32(Shift_Right(Ring_Phys_Addr, 32) mod 2 ** 32));
    Regs.Write(Dev.Buffer, Regs.RDBAL(Queue_Index), Interfaces.Unsigned_32(Ring_Phys_Addr mod 2 ** 32));

    Regs.Write(Dev.Buffer, Regs.RDLEN(Queue_Index), Ring_Size * 16);

    Regs.Write_Field(Dev.Buffer, Regs.SRRCTL(Queue_Index), Regs.SRRCTL_BSIZEPACKET, Packet_Buffer_Size / 1024);

    Regs.Set_Field(Dev.Buffer, Regs.SRRCTL(Queue_Index), Regs.SRRCTL_DROP_EN);

    Regs.Set_Field(Dev.Buffer, Regs.RXDCTL(Queue_Index), Regs.RXDCTL_ENABLE);
    if After_Timeout(1.0, true, Dev.Buffer, Regs.RXDCTL(Queue_Index), Regs.RXDCTL_ENABLE) then
      Text_IO.Put_Line("RXDCTL.ENABLE did not set, cannot enable queue");
      GNAT.OS_Lib.OS_Abort;
    end if;

    Regs.Write(Dev.Buffer, Regs.RDT(Queue_Index), Ring_Size - 1);

    if not Dev.RX_Enabled then
      Regs.Set_Field(Dev.Buffer, Regs.SECRXCTRL, Regs.SECRXCTRL_RX_DIS);

      if After_Timeout(1.0, true, Dev.Buffer, Regs.SECRXSTAT, Regs.SECRXSTAT_SECRX_RDY) then
        Text_IO.Put_Line("SECRXSTAT.SECRXRDY timed out, cannot start device");
        GNAT.OS_Lib.OS_Abort;
      end if;

      Regs.Set_Field(Dev.Buffer, Regs.RXCTRL, Regs.RXCTRL_RXEN);

      Regs.Clear_Field(Dev.Buffer, Regs.SECRXCTRL, Regs.SECRXCTRL_RX_DIS);

      Regs.Set_Field(Dev.Buffer, Regs.CTRLEXT, Regs.CTRLEXT_NSDIS);

      Dev.RX_Enabled := True;
    end if;

    Regs.Clear_Field(Dev.Buffer, Regs.DCARXCTRL(Queue_Index), Regs.DCARXCTRL_UNKNOWN);

    return Dev.Buffer(Device_Buffer_Range(Regs.RDT(Queue_Index) / 4))'Access;
  end;

  function Add_Output(Dev: not null access Device; Ring: not null access Descriptor_Ring; Head: not null access VolatileUInt32) return Register_Access is
    Queue_Index: Integer := 0;
    Ring_Phys_Addr: Interfaces.Unsigned_64;
    Head_Phys_Addr: Interfaces.Unsigned_64;
    function Get_Ring_Addr is new Environment.Get_Physical_Address(T => Descriptor);
    function Get_Head_Addr is new Environment.Get_Physical_Address(T => VolatileUInt32);
  begin
    loop
      if Queue_Index = Transmit_Queues_Count then
        Text_IO.Put_Line("No available transmit queues");
        GNAT.OS_Lib.OS_Abort;
      end if;
      exit when Regs.Is_Field_Cleared(Dev.Buffer, Regs.TXDCTL(Queue_Index), Regs.TXDCTL_ENABLE);
      Queue_Index := Queue_Index + 1;
    end loop;

    Ring_Phys_Addr := Interfaces.Unsigned_64(Get_Ring_Addr(Ring(0)'Access));
    Regs.Write(Dev.Buffer, Regs.TDBAH(Queue_Index), Interfaces.Unsigned_32(Shift_Right(Ring_Phys_Addr, 32) mod 2 ** 32));
    Regs.Write(Dev.Buffer, Regs.TDBAL(Queue_Index), Interfaces.Unsigned_32(Ring_Phys_Addr mod 2 ** 32));

    Regs.Write(Dev.Buffer, Regs.TDLEN(Queue_Index), Ring_Size * 16);

    Regs.Write_Field(Dev.Buffer, Regs.TXDCTL(Queue_Index), Regs.TXDCTL_PTHRESH, 60);
    Regs.Write_Field(Dev.Buffer, Regs.TXDCTL(Queue_Index), Regs.TXDCTL_HTHRESH, 4);

    Head_Phys_Addr := Interfaces.Unsigned_64(Get_Head_Addr(Head));
    if Head_Phys_Addr mod 16 /= 0 then
      Text_IO.Put_Line("Transmit head's physical address is not aligned properly");
      GNAT.OS_Lib.OS_Abort;
    end if;

    Regs.Write(Dev.Buffer, Regs.TDWBAH(Queue_Index), Interfaces.Unsigned_32(Shift_Right(Head_Phys_Addr, 32) mod 2 ** 32));
    Regs.Write(Dev.Buffer, Regs.TDWBAL(Queue_Index), Interfaces.Unsigned_32(Head_Phys_Addr mod 2 ** 32) or 1);

    Regs.Clear_Field(Dev.Buffer, Regs.DCATXCTRL(Queue_Index), Regs.DCATXCTRL_TX_DESC_WB_RO_EN);

    if not Dev.TX_Enabled then
      Regs.Set_Field(Dev.Buffer, Regs.DMATXCTL, Regs.DMATXCTL_TE);
      Dev.TX_Enabled := True;
    end if;

    Regs.Set_Field(Dev.Buffer, Regs.TXDCTL(Queue_Index), Regs.TXDCTL_ENABLE);
    if After_Timeout(1.0, true, Dev.Buffer, Regs.TXDCTL(Queue_Index), Regs.TXDCTL_ENABLE) then
      Text_IO.Put_Line("TXDCTL.ENABLE did not set, cannot enable queue");
      GNAT.OS_Lib.OS_Abort;
    end if;

    return Dev.Buffer(Device_Buffer_Range(Regs.TDT(Queue_Index) / 4))'Access;
  end;
end Ixgbe_Device;
