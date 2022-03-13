with Ixgbe_Queues; use Ixgbe_Queues;

package NF_Queues is
  Pool_Size: constant := 65535;
  Batch_Size: constant := 32;

  procedure Run(Rx0: in out Queue_Rx;
                Rx1: in out Queue_Rx;
                Tx0: in out Queue_Tx;
                Tx1: in out Queue_Tx)
       with No_Return, No_Inline;
end NF_Queues;
