with Ixgbe_Buffer_Pool; use Ixgbe_Buffer_Pool;
with Ixgbe_Device; use Ixgbe_Device;
with NF;

package body NF_Queues is
  procedure Run(Rx0: in out Queue_Rx;
                Rx1: in out Queue_Rx;
                Tx0: in out Queue_Tx;
                Tx1: in out Queue_Tx) is
    type Rx_Range is new Integer range 0 .. Batch_Size-1;
    type Rx_Array is array(Rx_Range) of Buffer_Access;
    function Rx is new Rx_Batch(R => Rx_Range, B => Rx_Array);
    Batch: Rx_Array := (others => Fake_Buffer'Access);
    Last_Rx: Rx_Range;
    Discard: Boolean;
  begin
    loop
      begin
        Last_Rx := Rx(Rx0, Batch)-1;
        for N in Batch'First..Last_Rx loop
          NF.Handle_Data(Batch(N).Data);
        end loop;
        declare
          type Tx_Range is new Rx_Range range 0 .. Last_Rx;
          type Tx_Array is array(Tx_Range) of Buffer_Access;
          function Tx is new Tx_Batch(R => Tx_Range, B => Tx_Array);
          Last_Tx: Tx_Range;
        begin
          Last_Tx := Tx(Tx1, Tx_Array(Batch(0 .. Last_Rx)))-1;
          for N in Rx_Range(Last_Tx+1)..Last_Rx loop
            Discard := Buffer_Pool_Give(Tx1.Pool, Batch(N));
          end loop;
        end;
      end;
    end loop;
  end;
end NF_Queues;
