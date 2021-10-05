package body Ixgbe_Regs is
  function CountTrailingZeroes(N: Interfaces.Unsigned_32) return Integer
    with Import => True,
         Convention => Intrinsic,
         External_Name => "__builtin_ctz";

  function Read(Buffer: access Dev_Buffer; Reg: in Interfaces.Unsigned_32) return Interfaces.Unsigned_32 is
  begin
    return Interfaces.Unsigned_32(From_Little(Buffer(Dev_Buffer_Range(Reg / 4))));
  end;

  function Read_Field(Buffer: access Dev_Buffer; Reg: in Interfaces.Unsigned_32; Field: in Interfaces.Unsigned_32) return Interfaces.Unsigned_32 is
    Value: Interfaces.Unsigned_32;
    Shift: Integer;
  begin
    Value := Read(Buffer, Reg);
    Shift := CountTrailingZeroes(Field);
    return Shift_Right(Value and Field, Shift);
  end;

  procedure Write(Buffer: access Dev_Buffer; Reg: in Interfaces.Unsigned_32; Value: Interfaces.Unsigned_32) is
  begin
    Buffer(Dev_Buffer_Range(Reg / 4)) := To_Little(Value);
  end;

  procedure Write_Field(Buffer: access Dev_Buffer; Reg: in Interfaces.Unsigned_32; Field: in Interfaces.Unsigned_32; Value: Interfaces.Unsigned_32) is
    Old_Value: Interfaces.Unsigned_32;
    Shift: Integer;
    New_Value: Interfaces.Unsigned_32;
  begin
    Old_Value := Read(Buffer, Reg);
    Shift := CountTrailingZeroes(Field);
    New_Value := (Old_Value and not Field) or Shift_Left(Value, Shift);
    Write(Buffer, Reg, New_Value);
  end;

  procedure Clear(Buffer: access Dev_Buffer; Reg: in Interfaces.Unsigned_32) is
  begin
    Write(Buffer, Reg, 0);
  end;

  procedure Clear_Field(Buffer: access Dev_Buffer; Reg: in Interfaces.Unsigned_32; Field: in Interfaces.Unsigned_32) is
  begin
    Write_Field(Buffer, Reg, Field, 0);
  end;

  procedure Set_Field(Buffer: access Dev_Buffer; Reg: in Interfaces.Unsigned_32; Field: in Interfaces.Unsigned_32) is
    Old_Value: Interfaces.Unsigned_32;
    New_Value: Interfaces.Unsigned_32;
  begin
    Old_Value := Read(Buffer, Reg);
    New_Value := Old_Value or Field;
    Write(Buffer, Reg, New_value);
  end;
end Ixgbe_Regs;
