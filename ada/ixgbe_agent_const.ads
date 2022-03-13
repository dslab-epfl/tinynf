with Ixgbe; use Ixgbe;
with Ixgbe_Device; use Ixgbe_Device;

generic
  type Outputs_Range is (<>);
package Ixgbe_Agent_Const is
  Flush_Period: constant := 8;
  Recycle_Period: constant := 64;

  type Packet_Outputs is array(Outputs_Range) of Packet_Length;

  type Processor is not null access procedure(Data: not null access Packet_Data;
                                              Length: in Packet_Length;
                                              Output_Lengths: not null access Packet_Outputs);

  type Packet_Array is array(Delimiter_Range) of aliased Packet_Data;
  type Descriptor_Ring_Array is array(Outputs_Range) of not null access Descriptor_Ring;
  type Transmit_Head_Access_Array is array(Outputs_Range) of not null access Transmit_Head;
  type Transmit_Tail_Array is array(Outputs_Range) of Register_Access;

  type Agent is record
    Packets: not null access Packet_Array;
    Rings: Descriptor_Ring_Array;
    Receive_Tail: Register_Access;
    Transmit_Heads: Transmit_Head_Access_Array;
    Transmit_Tails: Transmit_Tail_Array;
    Outputs: not null access Packet_Outputs;
    Process_Delimiter: Delimiter_Range;
  end record;

  type Output_Devices is array(Outputs_Range) of Device;
  function Create_Agent(Input_Device: in out Device; Output_Devs: in out Output_Devices) return Agent;
  procedure Run(This: in out Agent;
                Proc: in Processor)
       with Inline_Always; -- to mimic C "static inline"

end Ixgbe_Agent_Const;
