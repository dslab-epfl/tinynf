with Ixgbe_Device; use Ixgbe_Device;
with Ixgbe_Agent;

package NF is
  procedure Handle_Data(Data: in out Packet_Data) with Inline_Always;

  procedure Processor(Data: in out Packet_Data;
                      Length: in Packet_Length;
                      Output_Lengths: in out Ixgbe_Agent.Packet_Outputs)
            with Inline;

  procedure Run(Agent0: in out Ixgbe_Agent.Agent;
                Agent1: in out Ixgbe_Agent.Agent)
            with No_Return, No_Inline;
end NF;
