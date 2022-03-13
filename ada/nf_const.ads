with Ixgbe_Device; use Ixgbe_Device;
with Ixgbe_Agent_Const;

generic
  type Outputs_Range is (<>);
package NF_Const is
  package Agent is new Ixgbe_Agent_Const(Outputs_Range);

  procedure Processor(Data: in out Packet_Data;
                      Length: in Packet_Length;
                      Output_Lengths: not null access Agent.Packet_Outputs)
            with Inline;

  procedure Run(Agent0: in out Agent.Agent;
                Agent1: in out Agent.Agent)
            with No_Return, No_Inline;
end NF_Const;
