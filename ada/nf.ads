with Ixgbe_Agent;
with Ixgbe_Constants;

generic
  type Outputs_Range is (<>);
package NF is
  package Agent is new Ixgbe_Agent(Outputs_Range);

  procedure Processor(Data: in out Ixgbe_Constants.Packet_Data;
                      Length: in Agent.Packet_Length;
                      Output_Lengths: not null access Agent.Packet_Outputs)
            with Inline;
end NF;
