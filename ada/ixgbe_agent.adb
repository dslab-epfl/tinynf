with Interfaces; use Interfaces;

with Environment;

package body Ixgbe_Agent is
  -- default values for arrays of non-null accesses
  Fake_Head: aliased Transmit_Head;
  Fake_Ring: aliased Descriptor_Ring;
  Fake_Reg: aliased VolatileUInt32;

  -- TODO there's got to be a cleaner way than these _Sized types and intermediate values...
  function Create_Agent(Input_Device: in out Device; Output_Devs: in out Output_Devices) return Agent is
    function Allocate_Packets is new Environment.Allocate(T => Packet_Data, R => Delimiter_Range, T_Array => Packet_Array);
    Packets: not null access Packet_Array := Allocate_Packets;
    function Get_Packet_Address is new Environment.Get_Physical_Address(T => Packet_Data);

    subtype DRA_Sized is Descriptor_Ring_Array(0 .. Output_Devs'Length - 1);
    Rings_Sized: DRA_Sized := (others => Fake_Ring'Access);
    Rings: Descriptor_Ring_Array := Rings_Sized;
    function Allocate_Ring is new Environment.Allocate(T => Descriptor, R => Delimiter_Range, T_Array => Descriptor_Ring);

    -- this is slightly messy; we convert from access-of-array to array-of-access
    type THA_Range is new Natural range 0 .. Output_Devs'Length - 1;
    type Transmit_Head_Array is array(THA_Range) of aliased Transmit_Head;
    function Allocate_Heads is new Environment.Allocate(T => Transmit_Head, R => THA_Range, T_Array => Transmit_Head_Array);
    All_Heads: not null access Transmit_Head_Array := Allocate_Heads;
    Transmit_Heads: Transmit_Head_Access_Array(0 .. Output_Devs'Length - 1) := (others => Fake_Head'Access);

    subtype TTA_Sized is Transmit_Tail_Array(0 .. Output_Devs'Length - 1);
    Transmit_Tails_Sized: TTA_Sized := (others => Fake_Reg'Access);
    Transmit_Tails: Transmit_Tail_Array := Transmit_Tails_Sized;

    Outputs: Packet_Outputs(0 .. Output_Devs'Length - 1) := (others => Packet_Length(0));
  begin
    -- no idea why the .all'unchecked are needed but just like in Device it raises an access error otherwise

    for R in Rings'Range loop
      Rings(R) := Allocate_Ring.all'Unchecked_Access;
      for N in Delimiter_Range loop
        Rings(R)(N).Addr := To_Little(Interfaces.Unsigned_64(Get_Packet_Address(Packets(N)'Access)));
      end loop;
    end loop;

    for N in Transmit_Heads'Range loop
      Transmit_Heads(N) := All_Heads(THA_Range(N))'Access;
    end loop;

    for N in Transmit_Tails'Range loop
      Transmit_Tails(N) := Ixgbe_Device.Add_Output(Output_Devs(N), Rings(N), Transmit_Heads(N));
    end loop;

    return (Outputs_Max => Output_Devs'Length - 1,
            Packets => Packets.all'Unchecked_Access,
            Rings => Rings,
            Receive_Tail => Ixgbe_Device.Set_Input(Input_Device, Rings(0)),
            Transmit_Heads => Transmit_Heads,
            Transmit_Tails => Transmit_Tails,
            Outputs => Outputs,
            Process_Delimiter => 0);
  end;

  procedure Run(This: in out Agent;
                Proc: in Processor)
  is
    N: Integer range 0 .. Flush_Period;
    Receive_Metadata: Rx_Metadata;
    RS_Bit: Interfaces.Unsigned_64;
    Length: Packet_Length;
    Earliest_Transmit_Head: Interfaces.Unsigned_32; -- TODO can this be delimiter_range? it should be...
    Min_Diff: Interfaces.Unsigned_64;
    Head: Interfaces.Unsigned_32;
    Diff: Interfaces.Unsigned_64;
  begin
    N := 0;
    while N < Flush_Period loop
      Receive_Metadata := To_Rx_Metadata(From_Little(This.Rings(This.Rings'First)(This.Process_Delimiter).Metadata));
      exit when not Receive_Metadata.Descriptor_Done;

      Length := Receive_Metadata.Length;
      Proc(This.Packets(This.Process_Delimiter), Length, This.Outputs);

      RS_Bit := (if (This.Process_Delimiter mod Recycle_Period) = (Recycle_Period - 1) then Tx_Metadata_RS else 0);

      for M in This.Rings'Range loop --0 .. This.Outputs_Max loop
        This.Rings(M)(This.Process_Delimiter).Metadata := To_Little(Tx_Metadata_Length(This.Outputs(M)) or RS_Bit or Tx_Metadata_IFCS or Tx_Metadata_EOP);
        This.Outputs(M) := 0;
      end loop;

      This.Process_Delimiter := This.Process_Delimiter + 1;

      if RS_Bit /= 0 then
        Earliest_Transmit_Head := Interfaces.Unsigned_32(This.Process_Delimiter);
        Min_Diff := Interfaces.Unsigned_64'Last;
        for H of This.Transmit_Heads loop
          Head := From_Little(H.all.Value);
          Diff := Interfaces.Unsigned_64(Head) - Interfaces.Unsigned_64(This.Process_Delimiter);
          if Diff <= Min_Diff then
            Earliest_Transmit_Head := Head;
            Min_Diff := Diff;
          end if;
        end loop;

        This.Receive_Tail.all := VolatileUInt32(To_Little(Earliest_Transmit_Head));
      end if;

      N := N + 1;
    end loop;
    if N /= 0 then
      for T of This.Transmit_Tails loop
        T.all := VolatileUInt32(To_Little(Interfaces.Unsigned_32(This.Process_Delimiter)));
      end loop;
    end if;
  end Run;
end Ixgbe_Agent;
