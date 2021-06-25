package body Ixgbe.Agent is
  function Init_Agent return Agent is
  begin
    raise Program_Error;
    return Init_Agent;
  end Init_Agent;

  procedure Run(This: in out Agent;
                Proc: in Processor)
  is
    N: Integer range 0 .. Ixgbe.Constants.Flush_Period;
    M: Outputs_Range;
    Receive_Metadata: VolatileUInt64;
    Length: Packet_Length;
    RS_Bit: VolatileUInt64;
    Earliest_Transmit_Head: VolatileUInt32;
    Min_Diff: VolatileUInt64;
    Head: VolatileUInt32;
    Diff: VolatileUInt64;
  begin
    N := 0;
    while N < Ixgbe.Constants.Flush_Period loop
      Receive_Metadata := From_Little(This.Receive_Ring(This.Process_Delimiter).Metadata);
      exit when (Receive_Metadata and 16#00_00_00_01_00_00_00_00#) = 0;

      Length := Packet_Length(Receive_Metadata mod 2 ** 16);
      Proc(This.Packets(This.Process_Delimiter), Length, This.Outputs);

      RS_Bit := (if (This.Process_Delimiter mod Ixgbe.Constants.Recycle_Period) = (Ixgbe.Constants.Recycle_Period - 1) then 16#00_00_00_00_08_00_00_00# else 0);

      -- I cannot find a way to get GNAT to not emit bounds checks when using a single index for both :/
      M := 0;
      for R of This.Transmit_Rings.all loop
        R(This.Process_Delimiter).Metadata := To_Little(VolatileUInt64(This.Outputs(M)) or RS_Bit or 16#00_00_00_00_03_00_00_00#);
        This.Outputs(M) := 0;
        M := M + 1;
      end loop;

      This.Process_Delimiter := This.Process_Delimiter + 1;

      if RS_Bit /= 0 then
        Earliest_Transmit_Head := VolatileUInt32(This.Process_Delimiter);
        Min_Diff := VolatileUint64'Last;
        for H of This.Transmit_Heads.all loop
          Head := From_Little(H.Value);
          Diff := VolatileUInt64(Head) - VolatileUInt64(This.Process_Delimiter);
          if Diff <= Min_Diff then
            Earliest_Transmit_Head := Head;
            Min_Diff := Diff;
          end if;
        end loop;

        This.Receive_Tail.all := To_Little((Earliest_Transmit_Head - 1) mod (VolatileUInt32(Delimiter_Range'Last) + 1));
      end if;
    end loop;
    if N /= 0 then
      for T of This.Transmit_Tails.all loop
        T.all := To_Little(VolatileUInt32(This.Process_Delimiter));
      end loop;
    end if;
  end Run;
end Ixgbe.Agent;
