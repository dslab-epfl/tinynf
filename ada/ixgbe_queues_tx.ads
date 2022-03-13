with Ixgbe; use Ixgbe;
with Ixgbe_Buffer_Pool; use Ixgbe_Buffer_Pool;
with Ixgbe_Queues; use Ixgbe_Queues;

generic
  Size: in UnsignedInteger;
package Ixgbe_Queues_Tx is
  type R is new UnsignedInteger range 0 .. Size-1;
  type B is array(R) of Buffer_Access;
  function Tx_Batch(Queue: in out Queue_Tx; Buffers: in out B) return UnsignedInteger with Inline_Always;
end Ixgbe_Queues_Tx;
