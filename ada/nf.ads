with Ixgbe_Agent; use Ixgbe_Agent;

package NF is
  procedure Processor(Data: in out Packet_Data;
                      Length: in Packet_Length;
                      OutputLengths: not null access Packet_Outputs);
end NF;
