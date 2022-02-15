with Ixgbe; use Ixgbe;
with Ixgbe_Device; use Ixgbe_Device;

package Ixgbe_Agent is
  type Outputs_Range is mod 2 ** 3; -- max 8 outputs

  Flush_Period: constant := 8;
  Recycle_Period: constant := 64;

  -- WEIRD: This MUST be of size 64, otherwise the card locks up quickly (even the heatup in the benchmarks doesn't finish)
  type Packet_Length is mod 2 ** 16 with Size => 64;
  type Packet_Outputs is array(Outputs_Range range <>) of Packet_Length;

  type Processor is not null access procedure(Data: in out Packet_Data;
                                              Length: in Packet_Length;
                                              Output_Lengths: in out Packet_Outputs);

  -- TODO do we need these types to be explicit?
  type Packet_Array is array(Delimiter_Range) of aliased Packet_Data;
  type Descriptor_Ring_Array is array(Outputs_Range range <>) of not null access Descriptor_Ring;
  type Transmit_Head_Array is array(Outputs_Range range <>) of Transmit_Head;
  type Transmit_Tail_Array is array(Outputs_Range range <>) of Register_Access;

  type Agent(Outputs_Max: Outputs_Range) is record
    Packets: not null access Packet_Array;
    Rings: Descriptor_Ring_Array(0 .. Outputs_Max);
    Receive_Tail: Register_Access;
    Transmit_Heads: not null access Transmit_Head_Array; -- constraint not allowed here, can't (0 .. Outputs_Max); but this is only used once every Recycle_Period packets...
    Transmit_Tails: Transmit_Tail_Array(0 .. Outputs_Max);
    Outputs: Packet_Outputs(0 .. Outputs_Max);
    Process_Delimiter: Delimiter_Range;
  end record;

  type Output_Devices is array(Outputs_Range range <>) of not null access Device;
  function Create_Agent(Input_Device: not null access Device; Output_Devs: in out Output_Devices) return Agent;
  procedure Run(This: in out Agent;
                Proc: in Processor);

end Ixgbe_Agent;
