with Interfaces; use Interfaces;

with Ixgbe; use Ixgbe;

package Ixgbe_Regs is
  function Read(Buffer: access Device_Buffer; Reg: in Interfaces.Unsigned_32) return Interfaces.Unsigned_32;
  function Read_Field(Buffer: access Device_Buffer; Reg: in Interfaces.Unsigned_32; Field: in Interfaces.Unsigned_32) return Interfaces.Unsigned_32;
  procedure Write(Buffer: access Device_Buffer; Reg: in Interfaces.Unsigned_32; Value: Interfaces.Unsigned_32);
  procedure Write_Field(Buffer: access Device_Buffer; Reg: in Interfaces.Unsigned_32; Field: in Interfaces.Unsigned_32; Value: in Interfaces.Unsigned_32);
  procedure Clear(Buffer: access Device_Buffer; Reg: in Interfaces.Unsigned_32);
  procedure Clear_Field(Buffer: access Device_Buffer; Reg: in Interfaces.Unsigned_32; Field: in Interfaces.Unsigned_32);
  procedure Set_Field(Buffer: access Device_Buffer; Reg: in Interfaces.Unsigned_32; Field: in Interfaces.Unsigned_32);
  function Is_Field_Cleared(Buffer: access Device_Buffer; Reg: in Interfaces.Unsigned_32; Field: in Interfaces.Unsigned_32) return Boolean is (Read_Field(Buffer, Reg, Field) = 0);


  CTRL: constant := 16#00000# / 4;
  CTRL_MASTER_DISABLE: constant := 2#100#;
  CTRL_RST: constant := 2#100_0000_0000_0000_0000_0000_0000#; -- bit 26

  CTRLEXT: constant := 16#00018# / 4;
  CTRLEXT_NSDIS: constant := 2#1_0000_0000_0000_0000#; -- bit 16

  function DCARXCTRL(n: Integer) return Interfaces.Unsigned_32 is (Interfaces.Unsigned_32(if n <= 63 then (16#0100C# / 4 + 16#10#*n) else (16#0D00C# / 4 + 16#10#*(n-64))));
  DCARXCTRL_UNKNOWN: constant := 2#1_0000_0000_0000#; -- BIT(12)

  function DCATXCTRL(n: Integer) return Interfaces.Unsigned_32 is (Interfaces.Unsigned_32(16#0600C# / 4 + 16#10#*n));
  DCATXCTRL_TX_DESC_WB_RO_EN: constant := 2#1000_0000_0000#; -- BIT(11)

  DMATXCTL: constant := 16#04A80# / 4;
  DMATXCTL_TE: constant := 2#1#; -- BIT(0)

  DTXMXSZRQ: constant := 16#08100# / 4;
  DTXMXSZRQ_MAX_BYTES_NUM_REQ: constant := 2#1111_1111_1111#; -- BITS(0,11)

  EEC: constant := 16#10010# / 4;
  EEC_EE_PRES: constant := 2#1_0000_0000#; -- BIT(8)
  EEC_AUTO_RD: constant := 2#10_0000_0000#; -- BIT(9)

  function EIMC(n: Integer) return Interfaces.Unsigned_32 is (Interfaces.Unsigned_32(if n = 0 then 16#00888# / 4 else (16#00AB0# / 4 + (n - 1))));

  FCCFG: constant := 16#03D00# / 4;
  FCCFG_TFCE: constant := 2#1_1000#;-- BITS(3,4)

  function FCRTH(n: Integer) return Interfaces.Unsigned_32 is (Interfaces.Unsigned_32(16#03260# / 4 + n));
  FCRTH_RTH: constant := 2#0111_1111_1111_1110_0000#;-- BITS(5,18)

  FCTRL: constant := 16#05080# / 4;
  FCTRL_MPE: constant := 2#1_0000_0000#; -- BIT(8)
  FCTRL_UPE: constant := 2#10_0000_0000#; -- BIT(9)

  function FTQF(n: Integer) return Interfaces.Unsigned_32 is (Interfaces.Unsigned_32(16#0E600# / 4 + n));
  FTQF_QUEUE_ENABLE: constant := 2#1000_0000_0000_0000_0000_0000_0000_0000#; -- BIT(31)

  FWSM: constant := 16#10148# / 4;
  FWSM_EXT_ERR_IND: constant := 2#1_1111_1000_0000_0000_0000_0000#; -- BITS(19,24)

  GCREXT: constant := 16#11050# / 4;
  GCREXT_BUFFERS_CLEAR_FUNC: constant := 2#0100_0000_0000_0000_0000_0000_0000_0000#;-- BIT(30)

  HLREG0: constant := 16#04240# / 4;
  HLREG0_LPBK: constant := 2#1000_0000_0000_0000#; --BIT(15)

  MFLCN: constant := 16#04294# / 4;
  MFLCN_RFCE: constant := 2#1000#; -- BIT(3)

  function MPSAR(n: Integer) return Interfaces.Unsigned_32 is (Interfaces.Unsigned_32(16#0A600# / 4 + n));

  function MTA(n: Integer) return Interfaces.Unsigned_32 is (Interfaces.Unsigned_32(16#05200# / 4 + n));

  function PFUTA(n: Integer) return Interfaces.Unsigned_32 is (Interfaces.Unsigned_32(16#0F400# / 4 + n));

  function PFVLVF(n: Integer) return Interfaces.Unsigned_32 is (Interfaces.Unsigned_32(16#0F100# / 4 + n));

  function PFVLVFB(n: Integer) return Interfaces.Unsigned_32 is (Interfaces.Unsigned_32(16#0F200# / 4 + n));

  function RDBAH(n: Integer) return Interfaces.Unsigned_32 is (Interfaces.Unsigned_32(if n <= 63 then (16#01004# / 4 + 16#10#*n) else (16#0D004# / 4 + 16#10#*(n-64))));

  function RDBAL(n: Integer) return Interfaces.Unsigned_32 is (Interfaces.Unsigned_32(if n <= 63 then (16#01000# / 4 + 16#10#*n) else (16#0D000# / 4 + 16#10#*(n-64))));

  function RDLEN(n: Integer) return Interfaces.Unsigned_32 is (Interfaces.Unsigned_32(if n <= 63 then (16#01008# / 4 + 16#10#*n) else (16#0D008# / 4 + 16#10#*(n-64))));

  RDRXCTL: constant := 16#02F00# / 4;
  RDRXCTL_CRC_STRIP: constant := 2#10#; -- BIT(1)
  RDRXCTL_DMAIDONE: constant := 2#1000#; -- BIT(3)
  RDRXCTL_RSCFRSTSIZE: constant := 2#11_1110_0000_0000_0000_0000#; -- BITS(17,21)
  RDRXCTL_RSCACKC: constant := 2#10_0000_0000_0000_0000_0000_0000#; -- BIT(25)
  RDRXCTL_FCOE_WRFIX: constant := 2#100_0000_0000_0000_0000_0000_0000#; -- BIT(26)

  function RDT(n: Integer) return Interfaces.Unsigned_32 is (Interfaces.Unsigned_32(if n <= 63 then (16#01018# / 4 + 16#10#*n) else (16#0D018# / 4 + 16#10#*(n-64))));

  RTTDCS: constant := 16#04900# / 4;
  RTTDCS_ARBDIS: constant := 2#100_0000#; -- BIT(6)

  RTTDQSEL: constant := 16#04904# / 4;

  RTTDT1C: constant := 16#04908# / 4;

  RXCTRL: constant := 16#03000# / 4;
  RXCTRL_RXEN: constant := 2#1#; -- BIT(0)

  function RXDCTL(n: Integer) return Interfaces.Unsigned_32 is (Interfaces.Unsigned_32(if n <= 63 then (16#01028# / 4 + 16#10#*n) else (16#0D028# / 4 + 16#10#*(n-64))));
  RXDCTL_ENABLE: constant := 2#10_0000_0000_0000_0000_0000_0000#; -- BIT(25)

  function RXPBSIZE(n: Integer) return Interfaces.Unsigned_32 is (Interfaces.Unsigned_32(16#03C00# / 4 + n));

  SECRXCTRL: constant := 16#08D00# / 4;
  SECRXCTRL_RX_DIS: constant := 2#10#; -- BIT(1)

  SECRXSTAT: constant := 16#08D04# / 4;
  SECRXSTAT_SECRX_RDY: constant := 2#1#; -- BIT(0)

  function SRRCTL(n: Integer) return Interfaces.Unsigned_32 is (Interfaces.Unsigned_32(if n <= 63 then (16#01014# / 4 + 16#10#*n) else (16#0D014# / 4 + 16#10#*(n-64))));
  SRRCTL_BSIZEPACKET: constant := 2#1_1111#; -- BITS(0,4)
  SRRCTL_DROP_EN: constant := 2#1_0000_0000_0000_0000_0000_0000_0000#; -- BIT(28)

  STATUS: constant := 16#00008# / 4;
  STATUS_PCIE_MASTER_ENABLE_STATUS: constant := 2#1000_0000_0000_0000_0000#; -- BIT(19)

  function TDBAH(n: Integer) return Interfaces.Unsigned_32 is (Interfaces.Unsigned_32(16#06004# / 4 + 16#10#*n));

  function TDBAL(n: Integer) return Interfaces.Unsigned_32 is (Interfaces.Unsigned_32(16#06000# / 4 + 16#10#*n));

  function TDLEN(n: Integer) return Interfaces.Unsigned_32 is (Interfaces.Unsigned_32(16#06008# / 4 + 16#10#*n));

  function TDT(n: Integer) return Interfaces.Unsigned_32 is (Interfaces.Unsigned_32(16#06018# / 4 + 16#10#*n));

  function TDWBAH(n: Integer) return Interfaces.Unsigned_32 is (Interfaces.Unsigned_32(16#0603C# / 4 + 16#10#*n));

  function TDWBAL(n: Integer) return Interfaces.Unsigned_32 is (Interfaces.Unsigned_32(16#06038# / 4 + 16#10#*n));

  function TXDCTL(n: Integer) return Interfaces.Unsigned_32 is (Interfaces.Unsigned_32(16#06028# / 4 + 16#10#*n));
  TXDCTL_PTHRESH: constant := 2#111_1111#; -- BITS(0,6)
  TXDCTL_HTHRESH: constant := 2#111_1111_0000_0000#; -- BITS(8,14)
  TXDCTL_ENABLE: constant := 2#10_0000_0000_0000_0000_0000_0000#; -- BIT(25)

  function TXPBSIZE(n: Integer) return Interfaces.Unsigned_32 is (Interfaces.Unsigned_32(16#0CC00# / 4 + n));

  function TXPBTHRESH(n: Integer) return Interfaces.Unsigned_32 is (Interfaces.Unsigned_32(16#04950# / 4 + n));
  TXPBTHRESH_THRESH: constant := 2#11_1111_1111#; -- BITS(0,9)
end Ixgbe_Regs;
