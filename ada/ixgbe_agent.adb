with Interfaces; use Interfaces;

with Environment;

package body Ixgbe_Agent is
  -- default values for arrays of non-null accesses
  Fake_Head: aliased Transmit_Head;
  Fake_Ring: aliased Descriptor_Ring;
  Fake_Reg: aliased VolatileUInt32;

  function Create_Agent(Input_Device: in out Device; Output_Devs: in out Output_Devices) return Agent is
    function Allocate_Packets is new Environment.Allocate(T => Packet_Data, R => Delimiter_Range, T_Array => Packet_Data_Array);
    Buffers: not null access Packet_Data_Array := Allocate_Packets;
    function Get_Packet_Address is new Environment.Get_Physical_Address(T => Packet_Data);

    Rings: Descriptor_Ring_Array := (others => Fake_Ring'Access);
    function Allocate_Ring is new Environment.Allocate(T => Descriptor, R => Delimiter_Range, T_Array => Descriptor_Ring);

    -- this is slightly messy; we convert from access-of-array to array-of-access
    type Transmit_Head_Array is array(Outputs_Range) of aliased Transmit_Head;
    function Allocate_Heads is new Environment.Allocate(T => Transmit_Head, R => Outputs_Range, T_Array => Transmit_Head_Array);
    All_Heads: not null access Transmit_Head_Array := Allocate_Heads;
    Transmit_Heads: Transmit_Head_Access_Array := (others => Fake_Head'Access);

    Transmit_Tail_Addrs: Transmit_Tail_Array := (others => Fake_Reg'Unchecked_Access);

    function Allocate_Outputs is new Environment.Allocate(T => Packet_Length, R => Outputs_Range, T_Array => Packet_Outputs);
    Outputs: not null access Packet_Outputs := Allocate_Outputs;
--    Outputs: Packet_Outputs := (others => Packet_Length(0));
  begin
    -- no idea why the .all'unchecked are needed but just like in Device it raises an access error otherwise

    for R in Outputs_Range loop
      Rings(R) := Allocate_Ring.all'Unchecked_Access;
      for N in Delimiter_Range loop
        Rings(R)(N).Addr := To_Little(Interfaces.Unsigned_64(Get_Packet_Address(Buffers(N)'Access)));
      end loop;
    end loop;

    for N in Outputs_Range loop
      Transmit_Heads(N) := All_Heads(N)'Unchecked_Access;
    end loop;

    for N in Outputs_Range loop
      Transmit_Tail_Addrs(N) := Ixgbe_Device.Add_Output(Output_Devs(N), Rings(N), Transmit_Heads(N));
    end loop;

    return (Buffers => Buffers.all'Unchecked_Access,
            Rings => Rings,
            Receive_Tail_Addr => Ixgbe_Device.Set_Input(Input_Device, Rings(Outputs_Range'First)),
            Transmit_Heads => Transmit_Heads,
            Transmit_Tail_Addrs => Transmit_Tail_Addrs,
            Outputs => Outputs.all'Unchecked_Access,
            Processed_Delimiter => 0);
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
      Receive_Metadata := To_Rx_Metadata(From_Little(This.Rings(Outputs_Range'First)(This.Processed_Delimiter).Metadata));
      exit when not Receive_Metadata.Descriptor_Done;

      Length := Receive_Metadata.Length;
      Proc(This.Buffers(This.Processed_Delimiter)'Access, Length, This.Outputs);

      RS_Bit := (if (This.Processed_Delimiter mod Recycle_Period) = (Recycle_Period - 1) then Tx_Metadata_RS else 0);

      for M in Outputs_Range loop
        This.Rings(M)(This.Processed_Delimiter).Metadata := To_Little(Tx_Metadata_Length(This.Outputs(M)) or RS_Bit or Tx_Metadata_IFCS or Tx_Metadata_EOP);
        This.Outputs(M) := 0;
      end loop;

      This.Processed_Delimiter := This.Processed_Delimiter + 1;

      if RS_Bit /= 0 then
        Earliest_Transmit_Head := Interfaces.Unsigned_32(This.Processed_Delimiter);
        Min_Diff := Interfaces.Unsigned_64'Last;
        for H of This.Transmit_Heads loop
          Head := From_Little(H.Value);
          Diff := Interfaces.Unsigned_64(Head) - Interfaces.Unsigned_64(This.Processed_Delimiter);
          if Diff <= Min_Diff then
            Earliest_Transmit_Head := Head;
            Min_Diff := Diff;
          end if;
        end loop;

        This.Receive_Tail_Addr.all := VolatileUInt32(To_Little(Earliest_Transmit_Head));
      end if;

      N := N + 1;
    end loop;
    if N /= 0 then
      for T of This.Transmit_Tail_Addrs loop
        T.all := VolatileUInt32(To_Little(Interfaces.Unsigned_32(This.Processed_Delimiter)));
      end loop;
    end if;
  end Run;
end Ixgbe_Agent;
