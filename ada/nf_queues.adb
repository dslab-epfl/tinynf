with Ixgbe_Buffer_Pool; use Ixgbe_Buffer_Pool;
with Ixgbe_Device; use Ixgbe_Device;
with NF;

with Ixgbe_Queues_Rx;
--with Ixgbe_Queues_Tx;

package body NF_Queues is
  procedure Run(Rx0: in out Queue_Rx;
                Rx1: in out Queue_Rx;
                Tx0: in out Queue_Tx;
                Tx1: in out Queue_Tx) is
    package Rx is new Ixgbe_Queues_Rx(Size => Batch_Size);
    use Rx;
    Batch: Rx.B := (others => Fake_Buffer'Access);
    N_Rx: Rx.R_Full := 0;
    Nb_Rx: Rx.R_Full;
    Discard: Boolean;
  begin
    loop
      begin
        Nb_Rx := Rx.Rx_Batch(Rx0, Batch);
        while N_Rx < Nb_Rx loop
          NF.Handle_Data(Batch(Rx.R(N_Rx)).Data);
          N_Rx := N_Rx + 1;
        end loop;
--        declare
--          package Tx is new Ixgbe_Queues_Tx(N => Rx.R, Size => Nb_Rx);
--          use Tx;
--          Nb_Tx: Tx.R;
--        begin
--          Nb_Tx := Tx.Tx_Batch(Tx1, Tx.B(Batch(Rx.R'First .. Tx.R'Last-1)));
--          for N in Rx.R(Nb_Tx)..Nb_Rx-1 loop
--            Discard := Buffer_Pool_Give(Tx1.Pool, Batch(N));
--          end loop;
--        end;
      end;
    end loop;
  end;
end NF_Queues;
