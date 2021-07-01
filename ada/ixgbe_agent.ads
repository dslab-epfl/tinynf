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

  type Processor is not null access procedure(Data: in out Packet_Data;
                                              Length: in Packet_Length;
                                              OutputLengths: not null access Packet_Outputs);

  type Agent is private;
  type Output_Devs is array(Outputs_Range range <>) of not null access Ixgbe_Device.Dev;
  function Create_Agent(Input_Device: not null access Ixgbe_Device.Dev; Output_Devices: in out Output_Devs) return Agent;
  procedure Run(This: in out Agent;
                Proc: in Processor);

private
  type Packet_Array is array(Delimiter_Range) of aliased Packet_Data;
  type Descriptor_Ring_Array is array(Outputs_Range range <>) of not null access Descriptor_Ring;
  type Transmit_Head_Array is array(Outputs_Range range <>) of Transmit_Head;
  type Transmit_Tail_Array is array(Outputs_Range range <>) of Register_Access;

  type Agent is record
    Packets: not null access Packet_Array;
    Receive_Ring: not null access Descriptor_Ring;
    Transmit_Rings: not null access Descriptor_Ring_Array;
    Receive_Tail: Register_Access;
    Transmit_Heads: not null access Transmit_Head_Array;
    Transmit_Tails: not null access Transmit_Tail_Array;
    Outputs: not null access Packet_Outputs;
    Process_Delimiter: Delimiter_Range;
  end record;

end Ixgbe_Agent;
