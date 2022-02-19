with Interfaces;

-- Define the necessary volatile types and endianness conversions used in the driver

package Ixgbe is
  type VolatileUInt32 is mod 2 ** 32
    with Volatile, Size => 32;

  -- little-endian only for now
  function From_Little(Value: in Interfaces.Unsigned_32) return Interfaces.Unsigned_32 is (Value) with Inline_Always;
  function From_Little(Value: in Interfaces.Unsigned_64) return Interfaces.Unsigned_64 is (Value) with Inline_Always;
  function To_Little(Value: in Interfaces.Unsigned_32) return Interfaces.Unsigned_32 is (Value) with Inline_Always;
  function To_Little(Value: in Interfaces.Unsigned_64) return Interfaces.Unsigned_64 is (Value) with Inline_Always;

  type Device_Buffer_Range is mod 128 * 1024 / 4;
  type Device_Buffer is array(Device_Buffer_Range) of aliased VolatileUInt32;

  type Register_Access is not null access all VolatileUInt32;
end Ixgbe;
