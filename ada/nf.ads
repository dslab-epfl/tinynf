with Ixgbe_Device; use Ixgbe_Device;
with Ixgbe_Agent;

package NF is
  procedure Processor(Data: in out Packet_Data;
                      Length: in Ixgbe_Agent.Packet_Length;
                      Output_Lengths: in out Ixgbe_Agent.Packet_Outputs)
            with Inline;
end NF;
