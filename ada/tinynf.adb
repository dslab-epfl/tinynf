-- The GNAT doc says these are recommended and might improve perf:
-- https://docs.adacore.com/gnat_ugn-docs/html/gnat_ugn/gnat_ugn/gnat_and_program_execution.html 6.3.1.2
pragma Restrictions (No_Abort_Statements);
pragma Restrictions (Max_Asynchronous_Select_Nesting => 0);

with Ada.Command_Line;
with Text_IO;
with GNAT.OS_Lib;

with NF;
with NF_Const;
with NF_Queues;
with Pci_Parse;

with Ixgbe; use Ixgbe;
with Ixgbe_Agent; use Ixgbe_Agent;
with Ixgbe_Buffer_Pool; use Ixgbe_Buffer_Pool;
with Ixgbe_Device; use Ixgbe_Device;
with Ixgbe_Queues; use Ixgbe_Queues;

procedure TinyNF is
begin
  if Ada.Command_Line.Argument_Count /= 3 then
    Text_IO.Put_Line("Bad number of args, expected 3, first is TN_MODE");
    GNAT.OS_Lib.OS_Abort;
  end if;

  declare
    Dev0: Device := Init_Device(Pci_Parse.Parse_Address(Ada.Command_Line.Argument(2)));
    Dev1: Device := Init_Device(Pci_Parse.Parse_Address(Ada.Command_Line.Argument(3)));
    Mode: String := Ada.Command_Line.Argument(1);
  begin
    Set_Promiscuous(Dev0);
    Set_Promiscuous(Dev1);

    if Mode = "restricted" then
      declare
        Outs0: Output_Devices(0..0) := (0 => Dev1);
        Outs1: Output_Devices(0..0) := (0 => Dev0);
        Agent0: Agent := Create_Agent(Dev0, Outs0);
        Agent1: Agent := Create_Agent(Dev1, Outs1);
      begin
        Text_IO.Put_Line("Ada TinyNF starting...");
        NF.Run(Agent0, Agent1);
      end;

    elsif Mode = "const" then
      declare
        type Outputs_Range is range 0 .. 0;
        package NetFunc is new NF_Const(Outputs_Range);
        Outs0: NetFunc.Agent.Output_Devices := (others => Dev1);
        Outs1: NetFunc.Agent.Output_Devices := (others => Dev0);
        Agent0: NetFunc.Agent.Agent := NetFunc.Agent.Create_Agent(Dev0, Outs0);
        Agent1: NetFunc.Agent.Agent := NetFunc.Agent.Create_Agent(Dev1, Outs1);
      begin
        Text_IO.Put_Line("Ada TinyNF starting with const generics...");
        NetFunc.Run(Agent0, Agent1);
      end;

    elsif Mode = "flexible" then
      declare
        Pool0: aliased Buffer_Pool := Create_Buffer_Pool(NF_Queues.Pool_Size);
        Pool1: aliased Buffer_Pool := Create_Buffer_Pool(NF_Queues.Pool_Size);
        Rx0: Queue_Rx := Create_Queue_Rx(Dev0, Pool0'Access);
        Rx1: Queue_Rx := Create_Queue_Rx(Dev1, Pool1'Access);
        Tx0: Queue_Tx := Create_Queue_Tx(Dev0, Pool1'Access);
        Tx1: Queue_Tx := Create_Queue_Tx(Dev1, Pool0'Access);
      begin
        Text_IO.Put_Line("Ada queues starting...");
        NF_Queues.Run(Rx0, Rx1, Tx0, Tx1);
      end;

    end if;
  end;
end;
