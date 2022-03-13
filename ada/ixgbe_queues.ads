with Ixgbe; use Ixgbe;
with Ixgbe_Buffer_Pool; use Ixgbe_Buffer_Pool;
with Ixgbe_Device; use Ixgbe_Device;

package Ixgbe_Queues is
  -- for the queue itself
  type Buffer_Array is array(Delimiter_Range) of Buffer_Access;
  -- for RX/TX, we may not want a batch as large as Delimiter_Range itself
  type Buffer_Sub_Array is array(Delimiter_Range range <>) of Buffer_Access;

  type Queue_Rx is record
    Ring: not null access Descriptor_Ring;
    Buffers: not null access Buffer_Array;
    Pool: not null access Buffer_Pool;
    Receive_Tail_Addr: Register_Access;
    Next: Delimiter_Range;
  end record;

  function Create_Queue_Rx(Dev: in out Device; Pool: not null access Buffer_Pool) return Queue_Rx;
  function Rx_Batch(Queue: in out Queue_Rx; Buffers: Buffer_Sub_Array) return Delimiter_Range with Inline_Always;
end Ixgbe_Queues;
