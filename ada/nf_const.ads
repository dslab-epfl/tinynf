with Ixgbe_Device; use Ixgbe_Device;
with Ixgbe_Agent_Const;

generic
  type Outputs_Range is (<>);
package NF_Const is
  package Agent is new Ixgbe_Agent_Const(Outputs_Range);

  procedure Processor(Data: in out Packet_Data;
                      Length: in Agent.Packet_Length;
                      Output_Lengths: in out Agent.Packet_Outputs)
            with Inline;
end NF_Const;
