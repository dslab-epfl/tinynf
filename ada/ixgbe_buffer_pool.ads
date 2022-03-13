with Interfaces;
with System.Storage_Elements;

with Ixgbe_Device; use Ixgbe_Device;

package Ixgbe_Buffer_Pool is
  type Buffer is record
    Data: not null access Packet_Data;
    Phys_Addr: System.Storage_Elements.Integer_Address;
    Length: Interfaces.Unsigned_64;
  end record;

  type UnsignedInteger is mod Integer'Last;

  type Buffer_Access is not null access all Buffer;
  type Buffer_Access_Array is array(UnsignedInteger range <>) of Buffer_Access;

  -- NOTE: 'Max' here is one less than the desired side; cannot use 'Size-1' for the array ("discriminant in constraint must appear alone")
  type Buffer_Pool(Max: UnsignedInteger) is record
    Buffers: Buffer_Access_Array(0 .. Max);
    Index: UnsignedInteger;
  end record;

  function Buffer_Pool_Allocate(Size: in UnsignedInteger) return Buffer_Pool;
  function Buffer_Pool_Give(Pool: not null access Buffer_Pool; Buf: Buffer_Access) return Boolean with Inline_Always;
  function Buffer_Pool_Take(Pool: not null access Buffer_Pool) return access Buffer with Inline_Always;
end Ixgbe_Buffer_Pool;
