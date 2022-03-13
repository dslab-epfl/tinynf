with Interfaces;
with System.Storage_Elements;

with Environment;
with Ixgbe_Device; use Ixgbe_Device;

package body Ixgbe_Buffer_Pool is
  -- Fake data for the default value of non-null access types
  Fake_Data: aliased Packet_Data;
  Fake_Buffer: aliased Buffer := (Data => Fake_Data'Access, Phys_Addr => 0, Length => 0);

  function Buffer_Pool_Allocate(Size: in UnsignedInteger) return Buffer_Pool is
    type Buffer_Range is new UnsignedInteger range 0 .. Size - 1;

    type Buffer_Array is array(Buffer_Range) of aliased Buffer;
    function Buffer_Allocate is new Environment.Allocate(T => Buffer, R => Buffer_Range, T_Array => Buffer_Array);
    Buffers: not null access Buffer_Array := Buffer_Allocate;

    Buffer_Accesses: Buffer_Access_Array(0 .. Size - 1) := (others => Fake_Buffer'Access);

    type Data_Array is array(Buffer_Range) of aliased Packet_Data;
    function Data_Allocate is new Environment.Allocate(T => Packet_Data, R => Buffer_Range, T_Array => Data_Array);
    Data: not null access Data_Array := Data_Allocate;
    function Get_Data_Address is new Environment.Get_Physical_Address(T => Packet_Data);
  begin
    for N in Buffer_Range loop
      Buffers(N) := (Data => Data(N)'Access, Phys_Addr => Get_Data_Address(Data(N)'Access), Length => 0);
      Buffer_Accesses(UnsignedInteger(N)) := Buffers(N)'Access;
    end loop;
    return (Max => Size - 1, Buffers => Buffer_Accesses, Index => (Size - 2));
  end;

  -- Note the <= Max, since Max is inclusive here!

  function Buffer_Pool_Give(Pool: in out Buffer_Pool; Buf: not null access Buffer) return Boolean is
  begin
    Pool.Index := Pool.Index + 1;
    if Pool.Index <= Pool.Max then
      Pool.Buffers(Pool.Index) := Buffer_Access(Buf);
      return true;
    end if;

    Pool.Index := Pool.Index - 1;
    return false;
  end;

  function Buffer_Pool_Take(Pool: in out Buffer_Pool) return access Buffer is
  begin
    if Pool.Index <= Pool.Max then
      declare
        Buf: not null access Buffer := Pool.Buffers(Pool.Index);
      begin
        Pool.Index := Pool.Index - 1;
        return Buf;
      end;
    end if;

    return null;
  end;
end Ixgbe_Buffer_Pool;
