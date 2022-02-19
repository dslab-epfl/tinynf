with System;
with Interfaces; use Interfaces;
with Ada.Unchecked_Conversion;

with Environment;

package body Ixgbe_Agent_Const is
  -- default value for arrays of non-null accesses
  Fake_Ring: aliased Descriptor_Ring;
  Fake_Reg: aliased VolatileUInt32;

  function Create_Agent(Input_Device: in out Device; Output_Devs: in out Output_Devices) return Agent is
    function Allocate_Packets is new Environment.Allocate(T => Packet_Data, R => Delimiter_Range, T_Array => Packet_Array);
    Packets: not null access Packet_Array := Allocate_Packets;
    function Get_Packet_Address is new Environment.Get_Physical_Address(T => Packet_Data);

    Rings: Descriptor_Ring_Array := (others => Fake_Ring'Access);
    function Allocate_Ring is new Environment.Allocate(T => Descriptor, R => Delimiter_Range, T_Array => Descriptor_Ring);

    function Allocate_Heads is new Environment.Allocate(T => Transmit_Head, R => Outputs_Range, T_Array => Transmit_Head_Array);
    Transmit_Heads: not null access Transmit_Head_Array := Allocate_Heads;

    Transmit_Tails: Transmit_Tail_Array := (others => Fake_Reg'Unchecked_Access);

    Outputs: Packet_Outputs := (others => 0);
  begin
    for R in Rings'Range loop
      Rings(R) := Allocate_Ring.all'Unchecked_Access; -- why???
      for N in Delimiter_Range loop
        Rings(R)(N).Buffer := To_Little(Interfaces.Unsigned_64(Get_Packet_Address(Packets(N)'Access)));
      end loop;
    end loop;

    for N in Outputs_Range loop
      Transmit_Tails(N) := Ixgbe_Device.Add_Output(Output_Devs(N), Rings(N), Transmit_Heads(N)'Access);
    end loop;

    -- no idea why the .all'unchecked are needed but just like in Device it raises an access error otherwise
    return (Packets => Packets.all'Unchecked_Access,
            Rings => Rings,
            Receive_Tail => Ixgbe_Device.Set_Input(Input_Device, Rings(Outputs_Range'First)),
            Transmit_Heads => Transmit_Heads.all'Unchecked_Access,
            Transmit_Tails => Transmit_Tails,
            Outputs => Outputs,
            Process_Delimiter => 0);
  end;

  procedure Run(This: in out Agent;
                Proc: in Processor)
  is
    N: Integer range 0 .. Flush_Period;
    Receive_Metadata: Interfaces.Unsigned_64;
    RS_Bit: Interfaces.Unsigned_64;
    Length: Packet_Length;
    Earliest_Transmit_Head: Interfaces.Unsigned_32;
    Min_Diff: Interfaces.Unsigned_64;
    Head: Interfaces.Unsigned_32;
    Diff: Interfaces.Unsigned_64;

    -- This seems to be necessary to not generate any checks when truncating the 16-bit length from the rest of the metadata...
    -- Might as well use it for Descriptor Done while we're at it
    type Meta_Read is record
      Length: Packet_Length;
      DescriptorDone: Boolean;
    end record
      with Bit_Order => System.Low_Order_First,
           Size => 64;
    for Meta_Read use record
      Length at 0 range 0 .. 15;
      DescriptorDone at 0 range 32 .. 32;
    end record;
    function Meta_To_Read is new Ada.Unchecked_Conversion(Source => Interfaces.Unsigned_64, Target => Meta_Read);
  begin
    N := 0;
    while N < Flush_Period loop
      Receive_Metadata := From_Little(This.Rings(Outputs_Range'First)(This.Process_Delimiter).Metadata);
      exit when not Meta_To_Read(Receive_Metadata).DescriptorDone;

      Length := Meta_To_Read(Receive_Metadata).Length;
      Proc(This.Packets(This.Process_Delimiter), Length, This.Outputs);

      RS_Bit := (if (This.Process_Delimiter mod Recycle_Period) = (Recycle_Period - 1) then 16#00_00_00_00_08_00_00_00# else 0);

      for M in Outputs_Range loop
        This.Rings(M)(This.Process_Delimiter).Metadata := To_Little(Interfaces.Unsigned_64(This.Outputs(M)) or RS_Bit or 16#00_00_00_00_03_00_00_00#);
        This.Outputs(M) := 0;
      end loop;

      This.Process_Delimiter := This.Process_Delimiter + 1;

      if RS_Bit /= 0 then
        Earliest_Transmit_Head := Interfaces.Unsigned_32(This.Process_Delimiter);
        Min_Diff := Interfaces.Unsigned_64'Last;
        for H of This.Transmit_Heads.all loop
          Head := From_Little(H.Value);
          Diff := Interfaces.Unsigned_64(Head) - Interfaces.Unsigned_64(This.Process_Delimiter);
          if Diff <= Min_Diff then
            Earliest_Transmit_Head := Head;
            Min_Diff := Diff;
          end if;
        end loop;

        This.Receive_Tail.all := VolatileUInt32(To_Little((Earliest_Transmit_Head - 1) mod Ring_Size));
      end if;
      N := N + 1;
    end loop;
    if N /= 0 then
      for T of This.Transmit_Tails loop
        T.all := VolatileUInt32(To_Little(Interfaces.Unsigned_32(This.Process_Delimiter)));
      end loop;
    end if;
  end Run;
end Ixgbe_Agent_Const;
