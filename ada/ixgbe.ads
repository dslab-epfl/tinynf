with Interfaces;

with Ixgbe_Constants;

package Ixgbe is
  type VolatileUInt32 is mod 2 ** 32
    with Volatile, Size => 32;
  type VolatileUInt64 is mod 2 ** 64
    with Volatile, Size => 64;

  -- little-endian only for now
  function From_Little(Value: in VolatileUInt32) return VolatileUInt32 is (Value) with Inline_Always;
  function From_Little(Value: in VolatileUInt64) return VolatileUInt64 is (Value) with Inline_Always;
  function To_Little(Value: in VolatileUInt32) return VolatileUInt32 is (Value) with Inline_Always;
  function To_Little(Value: in VolatileUInt64) return VolatileUInt64 is (Value) with Inline_Always;

  type Descriptor is record
    Buffer: VolatileUInt64;
    Metadata: VolatileUInt64;
  end record
    with Pack;

  type Transmit_Head is record
    Value: aliased VolatileUInt32;
  end record
    with Pack, Alignment => 64; -- full cache line to avoid contention

  type Register_Access is not null access all VolatileUInt32;

  type Delimiter_Range is mod Ixgbe_Constants.Ring_Size;
  type Descriptor_Ring is array(Delimiter_Range) of aliased Descriptor;

  type Dev_Buffer_Range is new Integer range 0 .. 128 * 1024 / 4 - 1;
  type Dev_Buffer is array(Dev_Buffer_Range) of aliased VolatileUInt32;
end Ixgbe;
