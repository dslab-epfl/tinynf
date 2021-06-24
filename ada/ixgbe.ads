package Ixgbe is
  type VolatileUInt32 is mod 2 ** 32
    with Volatile;
  type VolatileUInt64 is mod 2 ** 64
    with Volatile;

  function From_Little(Value: in VolatileUInt32) return VolatileUInt32
    with Inline_Always;
  function From_Little(Value: in VolatileUInt64) return VolatileUInt64
    with Inline_Always;
  function To_Little(Value: in VolatileUInt32) return VolatileUInt32
    with Inline_Always;
  function To_Little(Value: in VolatileUInt64) return VolatileUInt64
    with Inline_Always;

  type Descriptor is record
    Buffer: VolatileUInt64;
    Metadata: VolatileUInt64;
  end record
    with Pack;

  type Transmit_Head is record
    Value: VolatileUInt32;
  end record;
  for Transmit_Head'Alignment use 64; -- full cache line to avoid contention
end Ixgbe;
