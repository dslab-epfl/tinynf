with Ixgbe_Buffer_Pool; use Ixgbe_Buffer_Pool;
with Ixgbe_Device; use Ixgbe_Device;
with NF;

package body NF_Queues is
  procedure Run(Rx0: in out Queue_Rx;
                Rx1: in out Queue_Rx;
                Tx0: in out Queue_Tx;
                Tx1: in out Queue_Tx) is
    type Buffer_Batch is new Buffer_Sub_Array(Batch_Size - 1);
    Batch: Buffer_Batch;
    TxBatch: Buffer_Sub_Array;
    Nb_Rx: Delimiter_Range;
    Nb_Tx: Delimiter_Range;
    Discard: Boolean;
  begin
    loop
      begin
        Nb_Rx := Rx_Batch(Rx0, Batch);
        for N in 0..Nb_Rx-1 loop
          NF.Handle_Data(Batch.Values(N).Data);
        end loop;
        TxBatch := (Last => Nb_Rx - 1, Values => Batch.Values(0 .. Nb_Rx - 1));
        Nb_Tx := Tx_Batch(Tx1, TxBatch);
        for N in Nb_Tx..Nb_Rx-1 loop
          Discard := Buffer_Pool_Give(Tx1.Pool, TxBatch.Values(N));
        end loop;
      end;
      begin
        Nb_Rx := Rx_Batch(Rx1, Batch);
        for N in 0..Nb_Rx-1 loop
          NF.Handle_Data(Batch.Values(N).Data);
        end loop;
        TxBatch := (Last => Nb_Rx - 1, Values => Batch.Values(0 .. Nb_Rx - 1));
        Nb_Tx := Tx_Batch(Tx0, TxBatch);
        for N in Nb_Tx..Nb_Rx-1 loop
          Discard := Buffer_Pool_Give(Tx0.Pool, TxBatch.Values(N));
        end loop;
      end;
    end loop;
  end;
end NF_Queues;
