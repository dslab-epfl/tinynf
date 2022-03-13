package body NF is
  procedure Handle_Data(Data: not null access Packet_Data) is
  begin
    Data(0) := 0;
    Data(1) := 0;
    Data(2) := 0;
    Data(3) := 0;
    Data(4) := 0;
    Data(5) := 1;
    Data(6) := 0;
    Data(7) := 0;
    Data(8) := 0;
    Data(9) := 0;
    Data(10) := 0;
    Data(11) := 0;
   end;

  procedure Processor(Data: not null access Packet_Data;
                      Length: in Packet_Length;
                      Output_Lengths: out Ixgbe_Agent.Packet_Outputs) is
  begin
    Handle_Data(Data);
    Output_Lengths(Output_Lengths'First) := Length;
  end;

  procedure Run(Agent0: in out Ixgbe_Agent.Agent;
                Agent1: in out Ixgbe_Agent.Agent) is
  begin
    loop
      Ixgbe_Agent.Run(Agent0, Processor'Access);
      Ixgbe_Agent.Run(Agent1, Processor'Access);
    end loop;
  end;
end NF;
