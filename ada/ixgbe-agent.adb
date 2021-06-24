package body Ixgbe.Agent is
  function InitAgent return Agent is
  begin
    raise Program_Error;
    return InitAgent;
  end InitAgent;

  procedure Run(This: in Agent;
                Proc: in Processor) is
  begin
    null;
  end Run;
end Ixgbe.Agent;
