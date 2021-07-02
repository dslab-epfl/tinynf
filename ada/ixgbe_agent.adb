with System;
with Ada.Unchecked_Conversion;

with Environment;

with Text_IO;

package body Ixgbe_Agent is
  -- default value for arrays of non-null accesses
  Fake_Ring: aliased Descriptor_Ring;

  function Create_Agent(Input_Device: not null access Ixgbe_Device.Dev; Output_Devices: in out Output_Devs) return Agent is
    function Allocate_Packets is new Environment.Allocate(T => Packet_Data, R => Delimiter_Range, T_Array => Packet_Array);
    Packets: not null access Packet_Array := Allocate_Packets;
    function Get_Packet_Address is new Environment.Get_Physical_Address(T => Packet_Data);

    subtype DRA_Sized is Descriptor_Ring_Array(Output_Devices'Range);
    Rings_Sized: not null access DRA_Sized := new DRA_Sized'(others => Fake_Ring'Access);
    Rings: not null access Descriptor_Ring_Array := Rings_Sized;
    function Allocate_Ring is new Environment.Allocate(T => Descriptor, R => Delimiter_Range, T_Array => Descriptor_Ring);

    subtype OD_Range is Outputs_Range range Output_Devices'First .. Output_Devices'Last; -- why do we need this? somehow passing 'Range as R => generic param doesn't wrk

    subtype THA_Sized is Transmit_Head_Array(OD_Range);
    function Allocate_Heads is new Environment.Allocate(T => Transmit_Head, R => OD_Range, T_Array => THA_Sized);
    Transmit_Heads_Sized: not null access THA_Sized := Allocate_Heads;
    Transmit_Heads: not null access Transmit_Head_Array := Transmit_Heads_Sized;

    subtype TTA_Sized is Transmit_Tail_Array(OD_Range);
    function Allocate_Tails is new Environment.Allocate(T => Register_Access, R => OD_Range, T_Array => TTA_Sized);
    Transmit_Tails_Sized: not null access TTA_Sized := Allocate_Tails;
    Transmit_Tails: not null access Transmit_Tail_Array := Transmit_Tails_Sized;

    function Allocate_Outputs is new Environment.Allocate(T => Packet_Length, R => Outputs_Range, T_Array => Packet_Outputs);
    Outputs: not null access Packet_Outputs := Allocate_Outputs;
  begin
    for R in Rings'Range loop
      Rings(R) := Allocate_Ring.all'Unchecked_Access; -- why???
      for N in Delimiter_Range loop
        Rings(R)(N).Buffer := To_Little(VolatileUInt64(Get_Packet_Address(Packets(N)'Access)));
      end loop;
    end loop;

    for N in OD_Range loop
      Transmit_Tails(N) := Ixgbe_Device.Add_Output(Output_Devices(N), Rings(N), Transmit_Heads(N).Value'Access);
    end loop;

    -- no idea why the .all'unchecked are needed but just like in Device it raises an access error otherwise
    return (Packets => Packets.all'Unchecked_Access,
            Receive_Ring => Rings(0),
            Transmit_Rings => Rings,
            Receive_Tail => Ixgbe_Device.Set_Input(Input_Device, Rings(0)),
            Transmit_Heads => Transmit_Heads.all'Unchecked_Access,
            Transmit_Tails => Transmit_Tails.all'Unchecked_Access,
            Outputs => Outputs.all'Unchecked_Access,
            Process_Delimiter => 0);
  end;

  procedure Run(This: in out Agent;
                Proc: in Processor)
  is
    N: Integer range 0 .. Ixgbe_Constants.Flush_Period;
    M: Outputs_Range;
    Receive_Metadata: VolatileUInt64;
    Length: Packet_Length;
    RS_Bit: VolatileUInt64;
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

--Text_IO.Put_Line("GOTCHA! " & Receive_Metadata'Image(Receive_Metadata));
      Length := Meta_To_Read(Receive_Metadata).Length;
      Proc(This.Packets(This.Process_Delimiter), Length, This.Outputs);

      RS_Bit := (if (This.Process_Delimiter rem Ixgbe_Constants.Recycle_Period) = (Ixgbe_Constants.Recycle_Period - 1) then 16#00_00_00_00_08_00_00_00# else 0);

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

        This.Receive_Tail.all := To_Little((Earliest_Transmit_Head - 1) rem (VolatileUInt32(Delimiter_Range'Last) + 1));
      end if;
    end loop;
    if N /= 0 then
      for T of This.Transmit_Tails.all loop
        T.all := To_Little(VolatileUInt32(This.Process_Delimiter));
      end loop;
    end if;
  end Run;
end Ixgbe_Agent;
