with Ada.Command_Line;
with Text_IO;
with GNAT.OS_Lib;

with Ixgbe_Agent; use Ixgbe_Agent;
with Ixgbe_Device; use Ixgbe_Device;
with NF;
with Pci_Parse;

procedure TinyNF is
begin
  if Ada.Command_Line.Argument_Count /= 2 then
    Text_IO.Put_Line("Bad number of args, expected 2");
    GNAT.OS_Lib.OS_Abort;
  end if;

  declare
    Dev0: aliased Dev := Init_Device(Pci_Parse.Parse_Address(Ada.Command_Line.Argument(1)));
    Dev1: aliased Dev := Init_Device(Pci_Parse.Parse_Address(Ada.Command_Line.Argument(2)));
    Outs0: Output_Devs := (0 => Dev1'Unchecked_Access);
    Outs1: Output_Devs := (0 => Dev0'Unchecked_Access);
    Agent0: Agent := Create_Agent(Dev0'Access, Outs0);
    Agent1: Agent := Create_Agent(Dev1'Access, Outs1);
  begin
    Text_IO.Put_Line("Ada TinyNF starting...");
    loop
      Run(Agent0, NF.Processor'Access);
      Run(Agent1, NF.Processor'Access);
    end loop;
  end;
end;
