package body Ixgbe.Agent is
  function Init_Agent return Agent is
  begin
    raise Program_Error;
    return Init_Agent;
  end Init_Agent;

  procedure Run(This: in out Agent;
                Proc: in Processor)
  is
    N: Integer range 0 .. 8;
    Receive_Metadata: VolatileUInt64;
    Length: Packet_Length;
    RS_Bit: VolatileUInt64;
    Earliest_Transmit_Head: VolatileUInt32;
    Min_Diff: VolatileUInt64;
    Head: VolatileUInt32;
    Diff: VolatileUInt64;

    Read_Descriptor_Done: constant VolatileUInt64 := 16#00_00_00_01_00_00_00_00#;
    Write_RS_Bit: constant VolatileUInt64 := 16#00_00_00_00_08_00_00_00#;
    Write_Descriptor_Done: constant VolatileUInt64 := 16#00_00_00_00_03_00_00_00#; -- also includes EOP
  begin
    -- for (n = 0; n < DriverConstants.FlushPeriod; n++) {
    N := 0;
    while N < 8 loop
      -- ulong receiveMetadata = Endianness.FromLittle(Volatile.Read(ref _receiveRing[_processDelimiter].Metadata));
      Receive_Metadata := From_Little(This.Receive_Ring(This.Process_Delimiter).Metadata);
      -- if ((receiveMetadata & (1ul << 32)) == 0) break;
      exit when (Receive_Metadata and Read_Descriptor_Done) = 0;

      -- ushort length = (ushort)receiveMetadata;
      Length := Packet_Length(Receive_Metadata);
      -- processor.Process(ref _packets[_processDelimiter], length, _outputs);
      Proc(This.Packets(This.Process_Delimiter), Length, This.Outputs);

      -- ulong rsBit = ((_processDelimiter % DriverConstants.RecyclePeriod) == (DriverConstants.RecyclePeriod - 1)) ? (1ul << (24 + 3)) : 0ul;
      RS_Bit := (if (This.Process_Delimiter mod 64) = 63 then Write_RS_Bit else 0);

      -- for (int b = 0; b < _transmitRings.Length; b++) {
      for N in This.Transmit_Rings'Range loop
      --   Volatile.Write(ref _transmitRings[b][_processDelimiter].Metadata, Endianness.ToLittle(_outputs[(byte)b] | rsBit | (1ul << (24 + 1)) | (1ul << 24)));
        This.Transmit_Rings(N)(This.Process_Delimiter).Metadata := To_Little(VolatileUInt64(This.Outputs(N)) or RS_Bit or Write_Descriptor_Done);
      --   _outputs[(byte)b] = 0;
        This.Outputs(N) := 0;
      -- }
      end loop;

      -- _processDelimiter++;
      This.Process_Delimiter := This.Process_Delimiter + 1;

      -- if (rsBit != 0) {
      if RS_Bit /= 0 then
        -- uint earliestTransmitHead = _processDelimiter;
        Earliest_Transmit_Head := VolatileUInt32(This.Process_Delimiter);
        -- ulong minDiff = ulong.MaxValue;
        Min_Diff := VolatileUint64'Last;
        -- foreach (ref var headRef in _transmitHeads) {
        for N in This.Transmit_Heads'Range loop --Head of This.TransmitHeads loop
          -- uint head = Endianness.FromLittle(Volatile.Read(ref headRef.Value));
          Head := From_Little(This.Transmit_Heads(N).Value);
          -- ulong diff = head - _processDelimiter;
          Diff := VolatileUInt64(Head) - VolatileUInt64(This.Process_Delimiter);
          -- if (diff <= minDiff) {
          if Diff <= Min_Diff then
            -- earliestTransmitHead = head;
            Earliest_Transmit_Head := Head;
            -- minDiff = diff;
            Min_Diff := Diff;
          end if;
          -- }
        -- }
        end loop;

        -- Volatile.Write(ref _receiveTail.Get(), Endianness.ToLittle((earliestTransmitHead - 1) % DriverConstants.RingSize));
        This.Receive_Tail.all := To_Little((Earliest_Transmit_Head - 1) mod (VolatileUInt32(Delimiter_Range'Last) + 1));
      -- }
      end if;
    -- }
    end loop;
    -- if (n != 0) {
    if N /= 0 then
      -- foreach (ref var tail in _transmitTails) {
      for N in This.Transmit_Tails'Range loop
        -- Volatile.Write(ref tail, Endianness.ToLittle(_processDelimiter));
        This.Transmit_Tails(N).all := To_Little(VolatileUInt32(This.Process_Delimiter));
      -- }
      end loop;
    -- }
    end if;
  end Run;
end Ixgbe.Agent;
