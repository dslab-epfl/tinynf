with System;
with Ada.Unchecked_Conversion;

with Environment;

package body Ixgbe_Agent is
  -- default values for arrays of non-null accesses
  Fake_Ring: aliased Descriptor_Ring;
--  Fake_Head: aliased Transmit_Head;

  function Create_Agent(Input_Device: not null access Ixgbe_Device.Dev; Output_Devices: in out Output_Devs) return Agent is
    function Allocate_Packets is new Environment.Allocate(T => Packet_Data, R => Delimiter_Range, T_Array => Packet_Array);
    function Allocate_Ring is new Environment.Allocate(T => Descriptor, R => Delimiter_Range, T_Array => Descriptor_Ring);
    function Allocate_Outputs is new Environment.Allocate(T => Packet_Length, R => Outputs_Range, T_Array => Packet_Outputs);

    Packets: Packet_Array;

    subtype DRA_Sized is Descriptor_Ring_Array(Output_Devices'Range);
    Transmit_Rings: not null access DRA_Sized := new DRA_Sized'(others => Fake_Ring'Access);

    subtype THA_Size is Outputs_Range range Output_Devices'First .. Output_Devices'Last;
    subtype THA_Sized is Transmit_Head_Array(THA_Size);
    function Allocate_Heads is new Environment.Allocate(T => Transmit_Head, R => THA_Size, T_Array => THA_Sized);
--    Transmit_Heads: not null access THA_Sized := --new THA_Sized'(others => Fake_Head'Access);
    Transmit_Heads: not null access THA_Sized := Allocate_Heads;


  begin
    raise Program_Error;
    return Create_Agent(Input_Device, Output_Devices);
--    return (Outputs => new PacketOutputs'()
--            ProcessDelimiter => 0);
--            _outputs = new Array256<ushort>(s => env.Allocate<ushort>(s).Span);

  --          _packets = new Array256<PacketData>(s => env.Allocate<PacketData>(s).Span);

    --        _transmitRings = new Array256Array<Descriptor>(outputDevices.Count, s => env.Allocate<Descriptor>(s).Span);
      --      for (int r = 0; r < _transmitRings.Length; r++)
--                for (int n = 0; n < 256; n++)
  --                  _transmitRings[r][(byte)n].Buffer = Endianness.ToLittle(env.GetPhysicalAddress(ref _packets[(byte)n]));

    --        _receiveRing = _transmitRings[0];
      --      _receiveTail = new Ref<uint>(inputDevice.SetInput(env, _receiveRing.AsSpan()).Span);

        --    _transmitHeads = env.Allocate<TransmitHead>((uint)outputDevices.Count).Span;
          --  _transmitTails = new RefArray<uint>(outputDevices.Count);
         --   for (byte n = 0; n < outputDevices.Count; n++)
--                _transmitTails[n] = outputDevices[n].AddOutput(env, _transmitRings[n].AsSpan(), ref _transmitHeads[n].Value).Span;
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
