with Ixgbe; use Ixgbe;
with Ixgbe_Device; use Ixgbe_Device;

package Ixgbe_Agent is
  Flush_Period: constant := 8;
  Recycle_Period: constant := 64;

  type Outputs_Range is mod 2 ** 8; -- max 256 outputs; TODO should be 8 but GNAT generates an "invalid data" check, why?

  -- WEIRD: This MUST be of size 64, otherwise the card locks up quickly (even the heatup in the benchmarks doesn't finish)
  type Packet_Length is mod 2 ** 16 with Size => 64;
  type Packet_Outputs is array(Outputs_Range) of Packet_Length;

  type Processor is not null access procedure(Data: in out Packet_Data;
                                              Length: in Packet_Length;
                                              Output_Lengths: in out Packet_Outputs);

  type Packet_Array is array(Delimiter_Range) of aliased Packet_Data;
  type Descriptor_Ring_Array is array(Outputs_Range range <>) of not null access Descriptor_Ring;
  type Transmit_Head_Array is array(Outputs_Range range <>) of aliased Transmit_Head;
  type Transmit_Tail_Array is array(Outputs_Range range <>) of Register_Access;

  type Agent(Outputs_Max: Outputs_Range) is record
    Packets: not null access Packet_Array;
    Rings: Descriptor_Ring_Array(0 .. Outputs_Max);
    Receive_Tail: Register_Access;
    Transmit_Heads: not null access Transmit_Head_Array; -- constraint not allowed here, can't (0 .. Outputs_Max); but this is only used once every Recycle_Period packets...
    Transmit_Tails: Transmit_Tail_Array(0 .. Outputs_Max);
    Outputs: Packet_Outputs;
    Process_Delimiter: Delimiter_Range;
  end record;

  type Output_Devices is array(Outputs_Range range <>) of Device;
  function Create_Agent(Input_Device: in out Device; Output_Devs: in out Output_Devices) return Agent;

  procedure Run(This: in out Agent; Proc: in Processor)
       with Inline_Always; -- to mimic C "static inline"

end Ixgbe_Agent;
