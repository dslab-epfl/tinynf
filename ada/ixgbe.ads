with System.Storage_Elements;

with Interfaces; use Interfaces;

package Ixgbe is
  type VolatileUInt32 is mod 2 ** 32
    with Volatile, Size => 32;
  type VolatileUInt64 is mod 2 ** 64
    with Volatile, Size => 64;

  -- little-endian only for now (the volatile-to-normal convs are for convenience of use)
  function From_Little(Value: in VolatileUInt32) return Interfaces.Unsigned_32 is (Interfaces.Unsigned_32(Value)) with Inline_Always;
  function From_Little(Value: in VolatileUInt64) return Interfaces.Unsigned_64 is (Interfaces.Unsigned_64(Value)) with Inline_Always;
  function To_Little(Value: in Interfaces.Unsigned_32) return VolatileUInt32 is (VolatileUInt32(Value)) with Inline_Always;
  function To_Little(Value: in Interfaces.Unsigned_64) return VolatileUInt64 is (VolatileUInt64(Value)) with Inline_Always;

  Packet_Buffer_Size: constant := 2 ** 11;
  Ring_Size: constant := 2 ** 8;
  Flush_Period: constant := 8;
  Recycle_Period: constant := 64;

  type Packet_Buffer_Length is mod Packet_Buffer_Size;
  type Packet_Data is array(Packet_Buffer_Length) of System.Storage_Elements.Storage_Element;

  type Descriptor is record
    Buffer: VolatileUInt64;
    Metadata: VolatileUInt64;
  end record
    with Pack;

  type Transmit_Head is record
    Value: aliased VolatileUInt32;
  end record
    with Size => 64*8,
         Alignment => 64; -- full cache line to avoid contention
  for Transmit_Head use record
    Value at 0 range 0 .. 31;
  end record;

  type Register_Access is not null access all VolatileUInt32;

  type Delimiter_Range is mod Ring_Size;
  type Descriptor_Ring is array(Delimiter_Range) of aliased Descriptor;

  type Dev_Buffer_Range is mod 128 * 1024 / 4;
  type Dev_Buffer is array(Dev_Buffer_Range) of aliased VolatileUInt32;
end Ixgbe;
