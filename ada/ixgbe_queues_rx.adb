with Ixgbe; use Ixgbe;
with Ixgbe_Buffer_Pool; use Ixgbe_Buffer_Pool;
with Ixgbe_Device; use Ixgbe_Device;

with Interfaces; use Interfaces;

package body Ixgbe_Queues_Rx is
  function Rx_Batch(Queue: in out Queue_Rx; Buffers: out B) return R_Full is
    Rx_Count: R_Full := 0;
    Metadata: Rx_Metadata;
    New_Buffer: access Buffer;
  begin
    -- Because Buffers must have at least one element, we use a do-while loop here
    loop
      Metadata := To_Rx_Metadata(From_Little(Queue.Ring(Queue.Next).Metadata));
      exit when not Metadata.Descriptor_Done;

      New_Buffer := Buffer_Pool_Take(Queue.Pool);
      exit when New_Buffer = null;

      Buffers(R(Rx_Count)) := Queue.Buffers(Queue.Next);
      Buffers(R(Rx_Count)).Length := Metadata.Length;

      Queue.Buffers(Queue.Next) := Buffer_Access(New_Buffer);
      Queue.Ring(Queue.Next).Addr := To_Little(Interfaces.Unsigned_64(New_Buffer.Phys_Addr));
      Queue.Ring(Queue.Next).Metadata := To_Little(0);

      Queue.Next := Queue.Next + 1;
      Rx_Count := Rx_Count + 1;
      exit when Rx_Count = R_Full'Last;
    end loop;
    if Rx_Count > 0 then
      Queue.Receive_Tail_Addr.all := VolatileUInt32(To_Little(Interfaces.Unsigned_32(Queue.Next - 1)));
    end if;
    return Rx_Count;
  end;
end Ixgbe_Queues_Rx;
