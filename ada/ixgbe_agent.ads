with System.Storage_Elements;
with Ixgbe; use Ixgbe;
with Ixgbe_Constants;
with Ixgbe_Device;

package Ixgbe_Agent is
  type Outputs_Range is mod 2 ** 8;
  type Packet_Buffer_Length is mod Ixgbe_Constants.Packet_Buffer_Size;
  type Packet_Length is mod 2 ** 16;

  type Packet_Data is array(Packet_Buffer_Length) of System.Storage_Elements.Storage_Element;
  type Packet_Outputs is array(Outputs_Range) of Packet_Length;

-- Ideally we'd use this as an argument to "Run", but GNAT won't inline it
-- which causes a perf loss for no good reason, so we directly call NF.Processor in the implementation instead...
--  type Processor is not null access procedure(Data: in out Packet_Data;
--                                              Length: in Packet_Length;
--                                              Output_Lengths: not null access Packet_Outputs);

  type Packet_Array is array(Delimiter_Range) of aliased Packet_Data;
  type Descriptor_Ring_Array is array(Outputs_Range range <>) of not null access Descriptor_Ring;
  type Transmit_Head_Array is array(Outputs_Range range <>) of Transmit_Head;
  type Transmit_Tail_Array is array(Outputs_Range range <>) of Register_Access;

  type Agent(N: Outputs_Range) is record
    Packets: not null access Packet_Array;
    Receive_Ring: not null access Descriptor_Ring;
    Transmit_Rings: Descriptor_Ring_Array(0 .. N);
    Receive_Tail: Register_Access;
    Transmit_Heads: not null access Transmit_Head_Array;
    Transmit_Tails: Transmit_Tail_Array(0 .. N);
    Outputs: not null access Packet_Outputs;
    Process_Delimiter: Delimiter_Range;
  end record;

  type Output_Devs is array(Outputs_Range range <>) of not null access Ixgbe_Device.Dev;
  function Create_Agent(Input_Device: not null access Ixgbe_Device.Dev; Output_Devices: in out Output_Devs) return Agent;
  procedure Run(This: in out Agent);
--                Proc: in Processor);

end Ixgbe_Agent;
