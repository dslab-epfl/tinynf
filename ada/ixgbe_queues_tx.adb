with Ixgbe_Buffer_Pool; use Ixgbe_Buffer_Pool;
with Ixgbe_Device; use Ixgbe_Device;

with Interfaces; use Interfaces;

package body Ixgbe_Queues_Tx is
  function Tx_Batch(Queue: in out Queue_Tx; Buffers: in B) return UnsignedInteger is
    Actual_Transmit_Head: Interfaces.Unsigned_32;
    Tx_Count: UnsignedInteger := 0;
    RS_Bit: Interfaces.Unsigned_64;
  begin
    if Queue.Next - Queue.Recycled_Head >= 2 * Recycle_Period then
      Actual_Transmit_Head := From_Little(Queue.Transmit_Head_Addr.all.Value);
      while Interfaces.Unsigned_32(Queue.Recycled_Head) /= Actual_Transmit_Head loop
        exit when not Buffer_Pool_Give(Queue.Pool, Queue.Buffers(Queue.Recycled_Head));
        Queue.Recycled_Head := Queue.Recycled_Head + 1;
      end loop;
    end if;

    -- Because Buffers must have at least one element... we want to use a do-while loop... but then GNAT inserts bounds checks :(
    -- even though it can figure out the Rx version just fine; this sounds like a bug.
    while Tx_Count <= UnsignedInteger(R'Last) loop
      exit when Queue.Next = Queue.Recycled_Head - 1;

      RS_Bit := (if (Queue.Next mod Recycle_Period) = (Recycle_Period - 1) then Tx_Metadata_RS else 0);
      Queue.Ring(Queue.Next).Addr := To_Little(Interfaces.Unsigned_64(Buffers(R(Tx_Count)).Phys_Addr));
      Queue.Ring(Queue.Next).Metadata := To_Little(Tx_Metadata_Length(Buffers(R(Tx_Count)).Length) or RS_Bit or Tx_Metadata_IFCS or Tx_Metadata_EOP);

      Queue.Buffers(Queue.Next) := Buffers(R(Tx_Count));

      Queue.Next := Queue.Next + 1;
      Tx_Count := Tx_Count + 1;
    end loop;
    if Tx_Count > 0 then
      Queue.Transmit_Tail_Addr.all := VolatileUInt32(To_Little(Interfaces.Unsigned_32(Queue.Next)));
    end if;
    return Tx_Count;
  end;
end Ixgbe_Queues_Tx;
