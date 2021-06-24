package Ixgbe.Pci_Regs is
   Bar0_Low: constant := 16#10#;
   Bar0_High: constant := 16#14#;

   Command: constant := 16#04#;
   Command_Memory_Access_Enable: constant := 2#01#;
   Command_Bus_Master_Enable: constant := 2#10#;
   Command_Interrupt_Disable: constant := 2#10_0000_0000#;

   DeviceStatus: constant := 16#AA#;
   DeviceStatus_TransactionPending: constant := 2#1_0000#;

   Id: constant := 16#00#;

   Pmcsr: constant := 16#44#;
   Pmcsr_Power_State: constant := 2#11#;
end Ixgbe.Pci_Regs;
