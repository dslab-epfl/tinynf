package body Ixgbe.Pci_Regs is
  function CountTrailingZeroes(N: Interfaces.Unsigned_32) return Integer
    with Import => True,
         Convention => Intrinsic,
         External_Name => "__builtin_ctz";

  function Read_Field(Addr: Pci_Address; Reg: Pci_Register; Field: Interfaces.Unsigned_32) return Interfaces.Unsigned_32 is
    Value: Interfaces.Unsigned_32;
    Shift: Integer;
  begin
    Value := Environment.Pci_Read(Addr, Reg);
    Shift := CountTrailingZeroes(Field);
    return Shift_Right(Value and Field, Shift);
  end;

  procedure Set_Field(Addr: Pci_Address; Reg: Pci_Register; Field: Interfaces.Unsigned_32) is
    Old_Value: Interfaces.Unsigned_32;
    New_Value: Interfaces.Unsigned_32;
  begin
    Old_Value := Environment.Pci_Read(Addr, Reg);
    New_Value := Old_Value or Field;
    Environment.Pci_Write(Addr, Reg, New_Value);
  end;
end Ixgbe.Pci_Regs;
