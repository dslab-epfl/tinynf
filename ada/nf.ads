with Ixgbe_Agent; use Ixgbe_Agent;

package NF is
  procedure Processor(Data: in out Packet_Data;
                      Length: in Packet_Length;
                      Output_Lengths: not null access Packet_Outputs)
            with Inline_Always;
end NF;
