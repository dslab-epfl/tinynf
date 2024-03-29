with Ixgbe; use Ixgbe;
with Ixgbe_Buffer_Pool; use Ixgbe_Buffer_Pool;
with Ixgbe_Device; use Ixgbe_Device;

package Ixgbe_Queues is
  -- for the queue itself
  type Buffer_Array is array(Delimiter_Range) of Buffer_Access;
  type Buffer_Sub_Array is array(Delimiter_Range range <>) of Buffer_Access;

  type Queue_Rx is record
    Ring: not null access Descriptor_Ring;
    Buffers: not null access Buffer_Array;
    Pool: not null access Buffer_Pool;
    Receive_Tail_Addr: Register_Access;
    Next: Delimiter_Range;
  end record;

  function Create_Queue_Rx(Dev: in out Device; Pool: not null access Buffer_Pool) return Queue_Rx;

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
end Ixgbe_Queues;
