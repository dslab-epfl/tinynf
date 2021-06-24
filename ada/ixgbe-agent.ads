with System.Storage_Elements;

package Ixgbe.Agent is
  type Outputs_Range is mod 2 ** 8;
  type Packet_Buffer_Length is mod 2 ** 11;
  type Packet_Length is mod 2 ** 16;

  type Packet_Data is array(Packet_Buffer_Length) of System.Storage_Elements.Storage_Element;
  type Packet_Outputs is array(Outputs_Range) of Packet_Length;

  type Processor is access procedure(Data: Packet_Data;
                                     Length: in Packet_Length;
                                     OutputLengths: access Packet_Outputs);

  type Agent is private;
  function Init_Agent return Agent;
  procedure Run(This: in out Agent;
                Proc: in Processor);

private
  type Delimiter_Range is mod 2 ** 8;

  type Packet_Array is array(Delimiter_Range) of Packet_Data;
  type Descriptor_Ring is array(Delimiter_Range) of Descriptor;
  type Descriptor_Ring_Array is array(Outputs_Range range <>) of access Descriptor_Ring;
  type Transmit_Head_Array is array(Outputs_Range range <>) of Transmit_Head;
  type Transmit_Tail_Array is array(Outputs_Range range <>) of access VolatileUInt32;

  type Agent is record
    Packets: access Packet_Array;
    Receive_Ring: access Descriptor_Ring;
    Transmit_Rings: access Descriptor_Ring_Array;
    Receive_Tail: access VolatileUInt32;
    Transmit_Heads: access Transmit_Head_Array;
    Transmit_Tails: access Transmit_Tail_Array;
    Outputs: access Packet_Outputs;
    Process_Delimiter: Delimiter_Range;
  end record;

end Ixgbe.Agent;
