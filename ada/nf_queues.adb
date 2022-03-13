with Ixgbe_Buffer_Pool; use Ixgbe_Buffer_Pool;
with Ixgbe_Device; use Ixgbe_Device;
with NF;

package body NF_Queues is
  procedure Run(Rx0: in out Queue_Rx;
                Rx1: in out Queue_Rx;
                Tx0: in out Queue_Tx;
                Tx1: in out Queue_Tx) is
    type Buffer_Batch is new Buffer_Sub_Array(0 .. Batch_Size - 1);
    Batch: Buffer_Batch := (others => Fake_Buffer'Access);
    Last_Rx: Delimiter_Range;
    Last_Tx: Delimiter_Range;
    Discard: Boolean;
  begin
    loop
      begin
        Last_Rx := Rx_Batch(Rx0, Batch);
        for N in Batch'First..Last_Rx loop
          NF.Handle_Data(Batch(N).Data);
        end loop;
        Last_Tx := Tx_Batch(Tx1, Batch(Batch'First .. Last_Rx));
        for N in Last_Tx+1..Last_Rx loop
          Discard := Buffer_Pool_Give(Tx1.Pool, Batch(N));
        end loop;
      end;
    end loop;
  end;
end NF_Queues;
