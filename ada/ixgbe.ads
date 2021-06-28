with Interfaces;

package Ixgbe is
  type VolatileUInt32 is mod 2 ** 32
    with Volatile;
  type VolatileUInt64 is mod 2 ** 64
    with Volatile;

  function From_Little(Value: in VolatileUInt32) return VolatileUInt32 is (Value);
  function From_Little(Value: in VolatileUInt64) return VolatileUInt64 is (Value);
  function To_Little(Value: in VolatileUInt32) return VolatileUInt32 is (Value);
  function To_Little(Value: in VolatileUInt64) return VolatileUInt64 is (Value);

  type Descriptor is record
    Buffer: VolatileUInt64;
    Metadata: VolatileUInt64;
  end record
    with Pack;

  type Transmit_Head is record
    Value: VolatileUInt32;
  end record;
  for Transmit_Head'Alignment use 64; -- full cache line to avoid contention

  type Dev_Buffer is array(Integer range <>) of VolatileUInt32;
  type Dev_Buffer_Access is access all Dev_Buffer;
end Ixgbe;
