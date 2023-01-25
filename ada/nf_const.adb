with NF;

package body NF_Const is
  procedure Processor(Data: not null access Packet_Data;
                      Length: in Packet_Length;
                      Output_Lengths: out Agent.Packet_Outputs) is
  begin
    NF.Handle(Data);
    Output_Lengths(Outputs_Range'First) := Length;
  end;

  procedure Run(Agent0: in out Agent.Agent;
                Agent1: in out Agent.Agent) is
  begin
    loop
      Agent.Run(Agent0, Processor'Access);
      Agent.Run(Agent1, Processor'Access);
    end loop;
  end;
end NF_Const;
