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

  function Rx_Batch(Queue: in out Queue_Rx; Buffers: out Buffer_Sub_Array) return Delimiter_Range is
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
    return (Ring => Ring,
            Buffers => Buffers,
            Pool => Pool,
            Transmit_Head_Addr => Head,
            Transmit_Tail_Addr => Ixgbe_Device.Add_Output(Dev, Ring, Head),
            Recycled_Head => 0,
            Next => 0);
  end;

  function Tx_Batch(Queue: in out Queue_Tx; Buffers: in Buffer_Sub_Array) return Delimiter_Range is
    Actual_Transmit_Head: Interfaces.Unsigned_32;
    Tx_Count: Delimiter_Range := 0;
    RS_Bit: Interfaces.Unsigned_64;
  begin
    if Queue.Next - Queue.Recycled_Head >= 2 * Recycle_Period then
      Actual_Transmit_Head := From_Little(Queue.Transmit_Head_Addr.all.Value);
      while Interfaces.Unsigned_32(Queue.Recycled_Head) /= Actual_Transmit_Head loop
        exit when not Buffer_Pool_Give(Queue.Pool, Queue.Buffers(Queue.Recycled_Head));
        Queue.Recycled_Head := Queue.Recycled_Head + 1;
      end loop;
    end if;

    while Tx_Count < Buffers.Values'Length loop
      exit when Queue.Next = Queue.Recycled_Head - 1;

      RS_Bit := (if (Queue.Next mod Recycle_Period) = (Recycle_Period - 1) then Tx_Metadata_RS else 0);
      Queue.Ring(Queue.Next).Addr := To_Little(Interfaces.Unsigned_64(Buffers.Values(Tx_Count).Phys_Addr));
      Queue.Ring(Queue.Next).Metadata := To_Little(Tx_Metadata_Length(Buffers.Values(Tx_Count).Length) or RS_Bit or Tx_Metadata_IFCS or Tx_Metadata_EOP);

      Queue.Buffers(Queue.Next) := Buffers.Values(Tx_Count);

      Queue.Next := Queue.Next + 1;
      Tx_Count := Tx_Count + 1;
    end loop;
    if Tx_Count > 0 then
      Queue.Transmit_Tail_Addr.all := VolatileUInt32(To_Little(Interfaces.Unsigned_32(Queue.Next)));
    end if;
    return Tx_Count;
  end;
end Ixgbe_Queues;
