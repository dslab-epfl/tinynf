with Interfaces;
with System.Storage_Elements;

with Ixgbe; use Ixgbe;
with Ixgbe_Device; use Ixgbe_Device;

package Ixgbe_Buffer_Pool is
  type Buffer is record
    Data: not null access Packet_Data;
    Phys_Addr: System.Storage_Elements.Integer_Address;
    Length: Packet_Length;
  end record;

  -- Fake data for the default value of non-null access types
  Fake_Data: aliased Packet_Data;
  Fake_Buffer: aliased Buffer := (Data => Fake_Data'Access, Phys_Addr => 0, Length => 0);

  type Buffer_Nullable_Access is access all Buffer;
  type Buffer_Access is not null access all Buffer;
  type Buffer_Access_Array is array(UnsignedInteger range <>) of Buffer_Access;

  -- NOTE: 'Max' here is one less than the desired size; cannot use 'Size-1' for the array ("discriminant in constraint must appear alone")
  type Buffer_Pool(Max: UnsignedInteger) is record
    Buffers: Buffer_Access_Array(0 .. Max);
    Index: UnsignedInteger;
  end record;

  function Create_Buffer_Pool(Size: in UnsignedInteger) return Buffer_Pool;
  function Buffer_Pool_Give(Pool: not null access Buffer_Pool; Buf: Buffer_Access) return Boolean with Inline_Always;
  function Buffer_Pool_Take(Pool: not null access Buffer_Pool) return Buffer_Nullable_Access with Inline_Always;
end Ixgbe_Buffer_Pool;
