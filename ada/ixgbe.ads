with Interfaces;

-- Define the necessary volatile types and endianness conversions used in the driver

package Ixgbe is
  type VolatileUInt8 is mod 2 ** 8
    with Volatile, Size => 8;
  type VolatileUInt32 is mod 2 ** 32
    with Volatile, Size => 32;
  type VolatileUInt64 is mod 2 ** 64
    with Volatile, Size => 64;

  -- little-endian only for now (the volatile-to-normal conversions are for convenience of use)
  function From_Little(Value: in VolatileUInt32) return Interfaces.Unsigned_32 is (Interfaces.Unsigned_32(Value)) with Inline_Always;
  function From_Little(Value: in VolatileUInt64) return Interfaces.Unsigned_64 is (Interfaces.Unsigned_64(Value)) with Inline_Always;
  function To_Little(Value: in Interfaces.Unsigned_32) return VolatileUInt32 is (VolatileUInt32(Value)) with Inline_Always;
  function To_Little(Value: in Interfaces.Unsigned_64) return VolatileUInt64 is (VolatileUInt64(Value)) with Inline_Always;

  type Device_Buffer_Range is mod 128 * 1024 / 4;
  type Device_Buffer is array(Device_Buffer_Range) of aliased VolatileUInt32;

  type Register_Access is not null access all VolatileUInt32;
end Ixgbe;
