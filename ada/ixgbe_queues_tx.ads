with Ixgbe_Buffer_Pool; use Ixgbe_Buffer_Pool;
with Ixgbe_Queues; use Ixgbe_Queues;

generic
  Size: in Integer;
package Ixgbe_Queues_Tx is
  type R_Full is new Integer range 0 .. Size;
  type R is new Integer range 0 .. Size-1;
  type B is array(R) of Buffer_Access;
  function Tx_Batch(Queue: in out Queue_Tx; Buffers: in out B) return R_Full with No_Inline;
end Ixgbe_Queues_Tx;
