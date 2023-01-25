with Ixgbe; use Ixgbe;
with Ixgbe_Device; use Ixgbe_Device;

package Ixgbe_Agent is
  Flush_Period: constant := 8;
  Recycle_Period: constant := 64;

  type Packet_Outputs is array(UnsignedInteger range <>) of Packet_Length;

  type Processor is not null access procedure(Data: not null access Packet_Data;
                                              Length: in Packet_Length;
                                              Output_Lengths: out Packet_Outputs);

  type Packet_Data_Array is array(Delimiter_Range) of aliased Packet_Data;
  type Descriptor_Ring_Array is array(UnsignedInteger range <>) of not null access Descriptor_Ring;
  type Transmit_Head_Access_Array is array(UnsignedInteger range <>) of not null access Transmit_Head;
  type Transmit_Tail_Array is array(UnsignedInteger range <>) of Register_Access;

  type Agent(Outputs_Max: UnsignedInteger) is record
    Buffers: not null access Packet_Data_Array;
    Rings: Descriptor_Ring_Array(0 .. Outputs_Max);
    Receive_Tail_Addr: Register_Access;
    Transmit_Heads: Transmit_Head_Access_Array(0 .. Outputs_Max);
    Transmit_Tail_Addrs: Transmit_Tail_Array(0 .. Outputs_Max);
    Outputs: Packet_Outputs(0 .. Outputs_Max);
    Processed_Delimiter: Delimiter_Range;
  end record;

  type Output_Devices is array(UnsignedInteger range <>) of Device;
  function Create_Agent(Input_Device: in out Device; Output_Devs: in out Output_Devices) return Agent;

  procedure Run(This: in out Agent; Proc: in Processor)
       with Inline_Always; -- to mimic C "static inline"

end Ixgbe_Agent;
