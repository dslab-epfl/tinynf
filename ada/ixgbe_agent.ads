with Ixgbe; use Ixgbe;
with Ixgbe_Device; use Ixgbe_Device;

package Ixgbe_Agent is
  Max_Outputs: constant := 8;
  type Outputs_Range is range 0 .. Max_Outputs;

  Flush_Period: constant := 8;
  Recycle_Period: constant := 64;

  -- WEIRD: This MUST be of size 64, otherwise the card locks up quickly (even the heatup in the benchmarks doesn't finish)
  type Packet_Length is mod 2 ** 16 with Size => 64;
  type Packet_Outputs is array(Outputs_Range range <>) of Packet_Length;

  type Processor is not null access procedure(Data: in out Packet_Data;
                                              Length: in Packet_Length;
                                              Output_Lengths: in out Packet_Outputs);

  -- TODO do we need these types to be explicit?
  type Packet_Array is array(Delimiter_Range) of aliased Packet_Data;
  type Descriptor_Ring_Array is array(Outputs_Range range <>) of not null access Descriptor_Ring;
  type Transmit_Head_Array is array(Outputs_Range range <>) of Transmit_Head;
  type Transmit_Tail_Array is array(Outputs_Range range <>) of Register_Access;


  -- NOTE: There's a tradeoff in terms of fidelity to C here; if Transmit_Heads and Outputs are allocated on the environment heap, as in C, then they can't be parameterized
  --       and conversely if they are parameterized then they must be allocated by Ada...
  --       we choose the parameterized version, it's unlikely the change of heaps would affect perf in any way (and anyway some non-C versions already rely on non-C heaps for objects)
  type Agent(Outputs_Max: Outputs_Range) is record
    Packets: not null access Packet_Array;
    Rings: Descriptor_Ring_Array(0 .. Outputs_Max);
    Receive_Tail: Register_Access;
    Transmit_Heads: Transmit_Head_Array(0 .. Outputs_Max);
    Transmit_Tails: Transmit_Tail_Array(0 .. Outputs_Max);
    Outputs: Packet_Outputs(0 .. Outputs_Max);
    Process_Delimiter: Delimiter_Range;
  end record;

  type Output_Devices is array(Outputs_Range range <>) of not null access Device;
  function Create_Agent(Input_Device: not null access Device; Output_Devs: in out Output_Devices) return Agent;
  procedure Run(This: in out Agent;
                Proc: in Processor);

end Ixgbe_Agent;
