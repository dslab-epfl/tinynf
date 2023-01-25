with Ixgbe; use Ixgbe;
with Ixgbe_Device; use Ixgbe_Device;

generic
  Outputs_Max: in UnsignedInteger;
package Ixgbe_Agent is
  Flush_Period: constant := 8;
  Recycle_Period: constant := 64;

  type Outputs_Range is new UnsignedInteger range 0 .. Outputs_Max;

  type Packet_Data_Array is array(Delimiter_Range) of aliased Packet_Data;
  type Descriptor_Ring_Array is array(Outputs_Range) of not null access Descriptor_Ring;
  type Transmit_Head_Access_Array is array(Outputs_Range) of not null access Transmit_Head;
  type Transmit_Tail_Array is array(Outputs_Range) of Register_Access;
  type Packet_Outputs is array(Outputs_Range) of Packet_Length;

  type Agent is record
    Buffers: not null access Packet_Data_Array;
    Rings: Descriptor_Ring_Array;
    Receive_Tail_Addr: Register_Access;
    Transmit_Heads: Transmit_Head_Access_Array;
    Transmit_Tail_Addrs: Transmit_Tail_Array;
    Outputs: not null access Packet_Outputs;
    Processed_Delimiter: Delimiter_Range;
  end record;

  type Output_Devices is array(Outputs_Range) of Device;
  function Create_Agent(Input_Device: in out Device; Output_Devs: in out Output_Devices) return Agent;

  generic
    with procedure Processor(Data: not null access Packet_Data;
                             Length: in Packet_Length;
                             Output_Lengths: not null access Packet_Outputs);
  procedure Run(This: in out Agent)
       with Inline_Always;

end Ixgbe_Agent;
