with Ixgbe; use Ixgbe;
with Ixgbe_Buffer_Pool; use Ixgbe_Buffer_Pool;
with Ixgbe_Device; use Ixgbe_Device;

package Ixgbe_Queues is
  -- for the queue itself
  type Buffer_Array is array(Delimiter_Range) of Buffer_Access;
  -- for RX/TX, we may not want a batch as large as Delimiter_Range itself
  -- but we want a lower bound for perf, thus we use a workaround as suggested in https://github.com/AdaCore/ada-spark-rfcs/blob/ec8f4066ce8302d2c0831a8cf8bb79cb8479b195/considered/rfc-lower-bound.rst
  type Buffer_Sub_Array_Inner is array(Delimiter_Range range <>) of Buffer_Access;
  type Buffer_Sub_Array(Last: Delimiter_Range) is record
    Values: Buffer_Sub_Array_Inner(0 .. Last);
  end record;

  type Queue_Rx is record
    Ring: not null access Descriptor_Ring;
    Buffers: not null access Buffer_Array;
    Pool: not null access Buffer_Pool;
    Receive_Tail_Addr: Register_Access;
    Next: Delimiter_Range;
  end record;

  function Create_Queue_Rx(Dev: in out Device; Pool: not null access Buffer_Pool) return Queue_Rx;
  function Rx_Batch(Queue: in out Queue_Rx; Buffers: in out Buffer_Sub_Array) return Delimiter_Range with Inline_Always;


  Recycle_Period: constant := 32;

  type Queue_Tx is record
    Ring: not null access Descriptor_Ring;
    Buffers: not null access Buffer_Array;
    Pool: not null access Buffer_Pool;
    Transmit_Head_Addr: not null access Transmit_Head;
    Transmit_Tail_Addr: Register_Access;
    Recycled_Head: Delimiter_Range;
    Next: Delimiter_Range;
  end record;

  function Create_Queue_Tx(Dev: in out Device; Pool: not null access Buffer_Pool) return Queue_Tx;
  function Tx_Batch(Queue: in out Queue_Tx; Buffers: in out Buffer_Sub_Array) return Delimiter_Range with Inline_Always;
end Ixgbe_Queues;
