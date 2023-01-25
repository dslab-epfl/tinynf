with Ixgbe; use Ixgbe;
with Ixgbe_Buffer_Pool; use Ixgbe_Buffer_Pool;
with Ixgbe_Device; use Ixgbe_Device;
with NF;

with Ixgbe_Queues_Rx;
with Ixgbe_Queues_Tx;

package body NF_Queues is
  procedure Run(Rx0: in out Queue_Rx;
                Rx1: in out Queue_Rx;
                Tx0: in out Queue_Tx;
                Tx1: in out Queue_Tx) is
    package Rx is new Ixgbe_Queues_Rx(Size => Batch_Size);
    use Rx;
    Batch: Rx.B := (others => Fake_Buffer'Access);
    Nb_Rx: Rx.R_Full;
    Discard: Boolean;
  begin
    loop
      declare
        N_Rx: Rx.R_Full := 0;
      begin
        Nb_Rx := Rx.Rx_Batch(Rx0, Batch);
        while N_Rx < Nb_Rx loop
          NF.Handle(Batch(Rx.R(N_Rx)).Data);
          N_Rx := N_Rx + 1;
        end loop;
        declare
          package Tx is new Ixgbe_Queues_Tx(Max => UnsignedInteger(Nb_Rx)-1);
          use Tx;
          Nb_Tx: UnsignedInteger;
        begin
          -- The semantics we'd like here are for Batch(0 .. Nb_Rx-1) to be an empty slice.
          -- But we cannot get that because the index has to be an Rx.R and -1 is not a valid Rx.R
          -- So we insert the check ourselves, which would need to be performed anyway if the semantics were the ones we want
          if Nb_Rx > 0 then
            Nb_Tx := Tx.Tx_Batch(Tx1, Tx.B(Batch(0 .. Rx.R(Nb_Rx-1))));
            while Nb_Tx < UnsignedInteger(Nb_Rx) loop
              Discard := Buffer_Pool_Give(Tx1.Pool, Batch(Rx.R(Nb_Tx)));
              Nb_Tx := Nb_Tx + 1;
            end loop;
          end if;
        end;
      end;
      declare
        N_Rx: Rx.R_Full := 0;
      begin
        Nb_Rx := Rx.Rx_Batch(Rx1, Batch);
        while N_Rx < Nb_Rx loop
          NF.Handle(Batch(Rx.R(N_Rx)).Data);
          N_Rx := N_Rx + 1;
        end loop;
        declare
          package Tx is new Ixgbe_Queues_Tx(Max => UnsignedInteger(Nb_Rx)-1);
          use Tx;
          Nb_Tx: UnsignedInteger;
        begin
          if Nb_Rx > 0 then
            Nb_Tx := Tx.Tx_Batch(Tx0, Tx.B(Batch(0 .. Rx.R(Nb_Rx-1))));
            while Nb_Tx < UnsignedInteger(Nb_Rx) loop
              Discard := Buffer_Pool_Give(Tx0.Pool, Batch(Rx.R(Nb_Tx)));
              Nb_Tx := Nb_Tx + 1;
            end loop;
          end if;
        end;
      end;
    end loop;
  end;
end NF_Queues;
