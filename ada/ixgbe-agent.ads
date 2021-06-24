with System.Storage_Elements;

package Ixgbe.Agent is
  type Packet_Data is array(Integer range 0 .. 2047) of System.Storage_Elements.Storage_Element;
  type Packet_Length is range 0 .. 65535;
  type Packet_Outputs is array(Integer range 0 .. 255) of Packet_Length;

  type Processor is access procedure(Data: in Packet_Data;
                                     Length: in Packet_Length;
                                     OutputLengths: out Packet_Outputs);

  type Agent is private;
  function InitAgent return Agent;
  procedure Run(This: in Agent;
                Proc: in Processor);

private
  type DelimiterRange is range 0 .. 255;

  type PacketArray is array(DelimiterRange) of Packet_Data;
  type DescriptorRing is array(DelimiterRange) of Descriptor;
  type DescriptorRingArray is array(Integer range <>) of access DescriptorRing;
  type TransmitHeadArray is array(Integer range <>) of TransmitHead;
  type TransmitTailArray is array(Integer range <>) of access UInt32;

  type Agent is record
    Packets: access PacketArray;
    ReceiveRing: access DescriptorRing;
    TransmitRings: access DescriptorRingArray;
    ReceiveTail: access UInt32;
    TransmitHeads: access TransmitHeadArray;
    TransmitTails: access TransmitTailArray;
    Outputs: access Packet_Outputs;
    ProcessDelimiter: DelimiterRange;
  end record;

end Ixgbe.Agent;
