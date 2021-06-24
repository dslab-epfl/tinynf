package body Ixgbe is
  function From_Little(Value: in VolatileUInt32) return VolatileUInt32 is begin return Value; end;
  function From_Little(Value: in VolatileUInt64) return VolatileUInt64 is begin return Value; end;
  function To_Little(Value: in VolatileUInt32) return VolatileUInt32 is begin return Value; end;
  function To_Little(Value: in VolatileUInt64) return VolatileUInt64 is begin return Value; end;
end Ixgbe;
