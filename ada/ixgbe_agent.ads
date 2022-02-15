with Ixgbe; use Ixgbe;
with Ixgbe_Device; use Ixgbe_Device;

generic
  type Outputs_Range is (<>);
package Ixgbe_Agent is
  -- WEIRD: This MUST be of size 64, otherwise the card locks up quickly (even the heatup in the benchmarks doesn't finish)
  type Packet_Length is mod 2 ** 16 with Size => 64;
  type Packet_Outputs is array(Outputs_Range) of Packet_Length;

  type Processor is not null access procedure(Data: in out Packet_Data;
                                              Length: in Packet_Length;
                                              Output_Lengths: not null access Packet_Outputs);

  type Packet_Array is array(Delimiter_Range) of aliased Packet_Data;
  type Descriptor_Ring_Array is array(Outputs_Range) of not null access Descriptor_Ring;
  type Transmit_Head_Array is array(Outputs_Range) of Transmit_Head;
  type Transmit_Tail_Array is array(Outputs_Range) of Register_Access;

  Flush_Period: constant := 8;
  Recycle_Period: constant := 64;

  type Agent is record
    Packets: not null access Packet_Array;
    Rings: Descriptor_Ring_Array;
    Receive_Tail: Register_Access;
    Transmit_Heads: not null access Transmit_Head_Array;
    Transmit_Tails: Transmit_Tail_Array;
    Outputs: not null access Packet_Outputs; -- this is a pointer so it does the same thing as the C code (allocated on the environment heap)
    Process_Delimiter: Delimiter_Range;
  end record;

  type Output_Devices is array(Outputs_Range) of not null access Device;
  function Create_Agent(Input_Device: not null access Device; Output_Devs: in out Output_Devices) return Agent;
  procedure Run(This: in out Agent;
                Proc: in Processor);

end Ixgbe_Agent;
