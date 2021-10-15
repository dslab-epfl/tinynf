with Ixgbe; use Ixgbe;
with Ixgbe_Device;

generic
  type Outputs_Range is (<>);
package Ixgbe_Agent is
  type Packet_Length is mod 2 ** 16 with Size => 64;
  type Packet_Outputs is array(Outputs_Range) of Packet_Length;

  type Processor is not null access procedure(Data: in out Packet_Data;
                                              Length: in Packet_Length;
                                              Output_Lengths: not null access Packet_Outputs);

  type Packet_Array is array(Delimiter_Range) of aliased Packet_Data;
  type Descriptor_Ring_Array is array(Outputs_Range) of not null access Descriptor_Ring;
  type Transmit_Head_Array is array(Outputs_Range) of Transmit_Head;
  type Transmit_Tail_Array is array(Outputs_Range) of Register_Access;

  type Agent is record
    Packets: not null access Packet_Array;
    Rings: Descriptor_Ring_Array;
    Receive_Tail: Register_Access;
    Transmit_Heads: not null access Transmit_Head_Array;
    Transmit_Tails: Transmit_Tail_Array;
    Outputs: not null access Packet_Outputs; -- this is a pointer so it does the same thing as the C code (allocated on the environment heap)
    Process_Delimiter: Delimiter_Range;
  end record;

  type Output_Devs is array(Outputs_Range) of not null access Ixgbe_Device.Dev;
  function Create_Agent(Input_Device: not null access Ixgbe_Device.Dev; Output_Devices: in out Output_Devs) return Agent;
  procedure Run(This: in out Agent;
                Proc: in Processor);

end Ixgbe_Agent;
