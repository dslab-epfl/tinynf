with Environment;
with Ixgbe; use Ixgbe;
with Ixgbe_Buffer_Pool; use Ixgbe_Buffer_Pool;
with Ixgbe_Device; use Ixgbe_Device;

with Interfaces; use Interfaces;
with Text_IO;
with GNAT.OS_Lib;

package body Ixgbe_Queues is
  function Create_Queue_Rx(Dev: in out Device; Pool: not null access Buffer_Pool) return Queue_Rx is
    function Allocate_Ring is new Environment.Allocate(T => Descriptor, R => Delimiter_Range, T_Array => Descriptor_Ring);
    Ring: not null access Descriptor_Ring := Allocate_Ring;

    function Allocate_Buffers is new Environment.Allocate(T => Buffer_Access, R => Delimiter_Range, T_Array => Buffer_Array);
    Buffers: not null access Buffer_Array := Allocate_Buffers;
  begin
    for N in Delimiter_Range loop
      declare
        Buf: Buffer_Nullable_Access := Buffer_Pool_Take(Pool);
      begin
        if Buf /= null then
          Buffers(N) := Buffer_Access(Buf);
          Ring(N).Addr := To_Little(Interfaces.Unsigned_64(Buffers(N).Phys_Addr));
          Ring(N).Metadata := To_Little(0);
        else
          Text_IO.Put_Line("Could not take a buffer for the RX queue");
          GNAT.OS_Lib.OS_Abort;
        end if;
      end;
    end loop;

    return (Ring => Ring.all'Unchecked_Access,
            Buffers => Buffers.all'Unchecked_Access,
            Pool => Pool.all'Unchecked_Access,
            Receive_Tail_Addr => Ixgbe_Device.Set_Input(Dev, Ring),
            Next => 0);
  end;


  function Create_Queue_Tx(Dev: in out Device; Pool: not null access Buffer_Pool) return Queue_Tx is
    function Allocate_Ring is new Environment.Allocate(T => Descriptor, R => Delimiter_Range, T_Array => Descriptor_Ring);
    Ring: not null access Descriptor_Ring := Allocate_Ring;

    function Allocate_Buffers is new Environment.Allocate(T => Buffer_Access, R => Delimiter_Range, T_Array => Buffer_Array);
    Buffers: not null access Buffer_Array := Allocate_Buffers;

    type Single_Range is range 0 .. 0;
    type Single_Transmit_Head is array(Single_Range) of aliased Transmit_Head;
    function Allocate_Head is new Environment.Allocate(T => Transmit_Head, R => Single_Range, T_Array => Single_Transmit_Head);
    Heads: not null access Single_Transmit_Head := Allocate_Head;
    Head: not null access Transmit_Head := Heads(Heads'First)'Access;
  begin
    return (Ring => Ring.all'Unchecked_Access,
            Buffers => Buffers.all'Unchecked_Access,
            Pool => Pool.all'Unchecked_Access,
            Transmit_Head_Addr => Head,
            Transmit_Tail_Addr => Ixgbe_Device.Add_Output(Dev, Ring, Head),
            Recycled_Head => 0,
            Next => 0);
  end;
end Ixgbe_Queues;
