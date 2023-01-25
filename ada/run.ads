with Ixgbe; use Ixgbe;
with Ixgbe_Device; use Ixgbe_Device;
with Ixgbe_Agent;
with Ixgbe_Queues; use Ixgbe_Queues;

package Run is
  procedure Handle(Data: not null access Packet_Data) with Inline_Always;

  generic
    with package Agent is new Ixgbe_Agent(<>);
  procedure Run(Agent0: in out Agent.Agent;
                Agent1: in out Agent.Agent) with No_Return, No_Inline;

  procedure Run_Queues(Rx0: in out Queue_Rx;
                       Rx1: in out Queue_Rx;
                       Tx0: in out Queue_Tx;
                       Tx1: in out Queue_Tx) with No_Return, No_Inline;
end Run;
