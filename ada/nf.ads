with Ixgbe_Constants;

generic
  type Outputs_Range is (<>);
package NF is
  type Packet_Length is mod 2 ** 16;
  type Packet_Outputs is array(Outputs_Range) of Packet_Length;

  procedure Processor(Data: in out Ixgbe_Constants.Packet_Data;
                      Length: in Packet_Length;
                      Output_Lengths: not null access Packet_Outputs)
            with Inline_Always;
end NF;
