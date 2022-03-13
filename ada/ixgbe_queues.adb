with Environment;
with Ixgbe; use Ixgbe;
with Ixgbe_Buffer_Pool; use Ixgbe_Buffer_Pool;
with Ixgbe_Device; use Ixgbe_Device;

with Interfaces;
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
        Buf: access Buffer := Buffer_Pool_Take(Pool);
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

    return (Ring => Ring,
            Buffers => Buffers,
            Pool => Pool,
            Receive_Tail_Addr => Ixgbe_Device.Set_Input(Dev, Ring),
            Next => 0);
  end;

  function Rx_Batch(Queue: in out Queue_Rx; Buffers: in out Buffer_Sub_Array) return Delimiter_Range is
    Rx_Count: Delimiter_Range := 0;
    Metadata: Rx_Metadata;
    New_Buffer: access Buffer;
  begin
    while Rx_Count < Buffers.Values'Length loop
      Metadata := To_Rx_Metadata(From_Little(Queue.Ring(Queue.Next).Metadata));
      exit when not Metadata.Descriptor_Done;

      New_Buffer := Buffer_Pool_Take(Queue.Pool);
      exit when New_Buffer = null;

      Buffers.Values(Rx_Count) := Queue.Buffers(Queue.Next);
      Buffers.Values(Rx_Count).Length := Metadata.Length;

      Queue.Buffers(Queue.Next) := Buffer_Access(New_Buffer);
      Queue.Ring(Queue.Next).Addr := To_Little(Interfaces.Unsigned_64(New_Buffer.Phys_Addr));
      Queue.Ring(Queue.Next).Metadata := To_Little(0);

      Queue.Next := Queue.Next + 1;
      Rx_Count := Rx_Count + 1;
    end loop;
    if Rx_Count > 0 then
      Queue.Receive_Tail_Addr.all := VolatileUInt32(To_Little(Interfaces.Unsigned_32(Queue.Next - 1)));
    end if;
    return Rx_Count;
  end;
end Ixgbe_Queues;
