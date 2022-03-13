with Ixgbe; use Ixgbe;
with Ixgbe_Buffer_Pool; use Ixgbe_Buffer_Pool;
with Ixgbe_Queues; use Ixgbe_Queues;

generic
  Size: in UnsignedInteger;
package Ixgbe_Queues_Rx is
  type R_Full is new UnsignedInteger range 0 .. Size;
  type R is new UnsignedInteger range 0 .. Size-1;
  type B is array(R) of Buffer_Access;
  function Rx_Batch(Queue: in out Queue_Rx; Buffers: out B) return R_Full with Inline_Always;
end Ixgbe_Queues_Rx;
