-- The GNAT doc says these are recommended and might improve perf:
-- https://docs.adacore.com/gnat_ugn-docs/html/gnat_ugn/gnat_ugn/gnat_and_program_execution.html 6.3.1.2
pragma Restrictions (No_Abort_Statements);
pragma Restrictions (Max_Asynchronous_Select_Nesting => 0);

with Ada.Command_Line;
with Text_IO;
with GNAT.OS_Lib;

with Ixgbe_Device; use Ixgbe_Device;
with Ixgbe_Agent;
with NF;
with NF_Const;
with Pci_Parse;

procedure TinyNF is
begin
  if Ada.Command_Line.Argument_Count /= 3 then
    Text_IO.Put_Line("Bad number of args, expected 3, first is TN_MODE");
    GNAT.OS_Lib.OS_Abort;
  end if;

  declare
    Dev0: aliased Device := Init_Device(Pci_Parse.Parse_Address(Ada.Command_Line.Argument(2)));
    Dev1: aliased Device := Init_Device(Pci_Parse.Parse_Address(Ada.Command_Line.Argument(3)));
    Mode: Integer := Integer'Value(Ada.Command_Line.Argument(1));
  begin
    Set_Promiscuous(Dev0);
    Set_Promiscuous(Dev1);

    if Mode = 0 then
      declare
        type Outputs_Range is range 0 .. 0 with Size => 64; -- TODO without Size? same below
        Outs0: Ixgbe_Agent.Output_Devices := (0 => Dev1'Unchecked_Access);
        Outs1: Ixgbe_Agent.Output_Devices := (0 => Dev0'Unchecked_Access);
        Agent0: Ixgbe_Agent.Agent := Ixgbe_Agent.Create_Agent(Dev0'Access, Outs0);
        Agent1: Ixgbe_Agent.Agent := Ixgbe_Agent.Create_Agent(Dev1'Access, Outs1);
      begin
        Text_IO.Put_Line("Ada TinyNF starting...");
        loop
          Ixgbe_Agent.Run(Agent0, NF.Processor'Access);
          Ixgbe_Agent.Run(Agent1, NF.Processor'Access);
        end loop;
      end;

    elsif Mode = 1 then

      declare
        type Outputs_Range is range 0 .. 0 with Size => 64;
        package NetFunc is new NF_Const(Outputs_Range);
        Outs0: NetFunc.Agent.Output_Devices := (others => Dev1'Unchecked_Access);
        Outs1: NetFunc.Agent.Output_Devices := (others => Dev0'Unchecked_Access);
        Agent0: NetFunc.Agent.Agent := NetFunc.Agent.Create_Agent(Dev0'Access, Outs0);
        Agent1: NetFunc.Agent.Agent := NetFunc.Agent.Create_Agent(Dev1'Access, Outs1);
      begin
        Text_IO.Put_Line("Ada TinyNF starting with const generics...");
        loop
          NetFunc.Agent.Run(Agent0, NetFunc.Processor'Access);
          NetFunc.Agent.Run(Agent1, NetFunc.Processor'Access);
        end loop;
      end;

    end if;
  end;
end;
