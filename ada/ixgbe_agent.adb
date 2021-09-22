with System;
with Ada.Unchecked_Conversion;

with Environment;

package body Ixgbe_Agent is
  -- default value for arrays of non-null accesses
  Fake_Ring: aliased Descriptor_Ring;
  Fake_Reg: aliased VolatileUInt32;

  function Create_Agent(Input_Device: not null access Ixgbe_Device.Dev; Output_Devices: in out Output_Devs) return Agent is
    function Allocate_Packets is new Environment.Allocate(T => Ixgbe_Constants.Packet_Data, R => Delimiter_Range, T_Array => Packet_Array);
    Packets: not null access Packet_Array := Allocate_Packets;
    function Get_Packet_Address is new Environment.Get_Physical_Address(T => Ixgbe_Constants.Packet_Data);

    Rings: Descriptor_Ring_Array := (others => Fake_Ring'Access);
    function Allocate_Ring is new Environment.Allocate(T => Descriptor, R => Delimiter_Range, T_Array => Descriptor_Ring);

    function Allocate_Heads is new Environment.Allocate(T => Transmit_Head, R => Outputs_Range, T_Array => Transmit_Head_Array);
    Transmit_Heads: not null access Transmit_Head_Array := Allocate_Heads;

    Transmit_Tails: Transmit_Tail_Array := (others => Fake_Reg'Unchecked_Access);

    function Allocate_Outputs is new Environment.Allocate(T => Packet_Length, R => Outputs_Range, T_Array => Packet_Outputs);
    Outputs: not null access Packet_Outputs := Allocate_Outputs;
  begin
    for R in Rings'Range loop
      Rings(R) := Allocate_Ring.all'Unchecked_Access; -- why???
      for N in Delimiter_Range loop
        Rings(R)(N).Buffer := To_Little(VolatileUInt64(Get_Packet_Address(Packets(N)'Access)));
      end loop;
    end loop;

    for N in Outputs_Range loop
      Transmit_Tails(N) := Ixgbe_Device.Add_Output(Output_Devices(N), Rings(N), Transmit_Heads(N).Value'Access);
    end loop;

    -- no idea why the .all'unchecked are needed but just like in Device it raises an access error otherwise
    return (Packets => Packets.all'Unchecked_Access,
            Receive_Ring => Rings(Outputs_Range'First),
            Transmit_Rings => Rings,
            Receive_Tail => Ixgbe_Device.Set_Input(Input_Device, Rings(Outputs_Range'First)),
            Transmit_Heads => Transmit_Heads.all'Unchecked_Access,
            Transmit_Tails => Transmit_Tails,
            Outputs => Outputs.all'Unchecked_Access,
            Process_Delimiter => 0);
  end;

  procedure Run(This: in out Agent;
                Proc: in Processor)
  is
    N: Integer range 0 .. Ixgbe_Constants.Flush_Period;
    Receive_Metadata: VolatileUInt64;
    RS_Bit: VolatileUInt64;
    Length: Packet_Length;
    Earliest_Transmit_Head: VolatileUInt32;
    Min_Diff: VolatileUInt64;
    Head: VolatileUInt32;
    Diff: VolatileUInt64;

    -- This seems to be necessary to not generate any checks when truncating the 16-bit length from the rest of the metadata...
    type Meta_Read is record
      Length: Packet_Length;
      Unused: Integer;
    end record;
    for Meta_Read use record
      Length at 0 range 0 .. 15;
      Unused at 0 range 16 .. 63;
    end record;
    for Meta_Read'Bit_Order use System.Low_Order_First;
    for Meta_Read'Size use 64;
    function Meta_To_Read is new Ada.Unchecked_Conversion(Source => VolatileUInt64, Target => Meta_Read);
  begin
    N := 0;
    while N < Ixgbe_Constants.Flush_Period loop
      Receive_Metadata := From_Little(This.Receive_Ring(This.Process_Delimiter).Metadata);
      exit when (Receive_Metadata and 16#00_00_00_01_00_00_00_00#) = 0;

      Length := Meta_To_Read(Receive_Metadata).Length;
      Proc(This.Packets(This.Process_Delimiter), Length, This.Outputs);

      RS_Bit := (if (This.Process_Delimiter rem Ixgbe_Constants.Recycle_Period) = (Ixgbe_Constants.Recycle_Period - 1) then 16#00_00_00_00_08_00_00_00# else 0);

      for M in Outputs_Range loop
        This.Transmit_Rings(M)(This.Process_Delimiter).Metadata := To_Little(VolatileUInt64(This.Outputs(M)) or RS_Bit or 16#00_00_00_00_03_00_00_00#);
        This.Outputs(M) := 0;
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

        This.Receive_Tail.all := To_Little((Earliest_Transmit_Head - 1) rem VolatileUInt32(Ixgbe_Constants.Ring_Size));
      end if;
      N := N + 1;
    end loop;
    if N /= 0 then
      for T of This.Transmit_Tails loop
        T.all := To_Little(VolatileUInt32(This.Process_Delimiter));
      end loop;
    end if;
  end Run;
end Ixgbe_Agent;
