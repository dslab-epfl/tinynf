-- The GNAT doc says these are recommended and might improve perf:
-- https://docs.adacore.com/gnat_ugn-docs/html/gnat_ugn/gnat_ugn/gnat_and_program_execution.html 6.3.1.2
pragma Restrictions (No_Abort_Statements);
pragma Restrictions (Max_Asynchronous_Select_Nesting => 0);

with Ada.Command_Line;
with Text_IO;
with GNAT.OS_Lib;

with Ixgbe_Agent;
with Ixgbe_Constants; use Ixgbe_Constants;
with Ixgbe_Device; use Ixgbe_Device;
with NF;
with Pci_Parse;

procedure TinyNF is
  type Outputs_Range is range 0 .. 0;
  package NetFunc is new NF(Outputs_Range);
begin
  if Ada.Command_Line.Argument_Count /= 2 then
    Text_IO.Put_Line("Bad number of args, expected 2");
    GNAT.OS_Lib.OS_Abort;
  end if;

  Text_IO.Put_Line("Ada TinyNF initializing...");

  declare
    Dev0: aliased Dev := Init_Device(Pci_Parse.Parse_Address(Ada.Command_Line.Argument(1)));
    Dev1: aliased Dev := Init_Device(Pci_Parse.Parse_Address(Ada.Command_Line.Argument(2)));
    Outs0: NetFunc.Agent.Output_Devs := (0 => Dev1'Unchecked_Access);
    Outs1: NetFunc.Agent.Output_Devs := (0 => Dev0'Unchecked_Access);
    Agent0: NetFunc.Agent.Agent := NetFunc.Agent.Create_Agent(Dev0'Access, Outs0);
    Agent1: NetFunc.Agent.Agent := NetFunc.Agent.Create_Agent(Dev1'Access, Outs1);
  begin
    Set_Promiscuous(Dev0);
    Set_Promiscuous(Dev1);
    Text_IO.Put_Line("Ada TinyNF starting...");
    loop
      NetFunc.Agent.Run(Agent0, NetFunc.Processor'Access);
      NetFunc.Agent.Run(Agent1, NetFunc.Processor'Access);
    end loop;
  end;
end;
