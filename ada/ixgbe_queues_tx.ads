with Ixgbe_Buffer_Pool; use Ixgbe_Buffer_Pool;
with Ixgbe_Queues; use Ixgbe_Queues;

generic
  type N is range <>;
  Size: N;
package Ixgbe_Queues_Tx is
  type R is new N range 0 .. Size;
  type B is array(0 .. Size-1) of Buffer_Access;
  function Tx_Batch(Queue: in out Queue_Tx; Buffers: in B) return R with Inline_Always;
end Ixgbe_Queues_Tx;
