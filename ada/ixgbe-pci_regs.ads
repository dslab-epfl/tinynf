with Interfaces; use Interfaces;

with Environment; use Environment;

package Ixgbe.Pci_Regs is
   function Read_Field(Addr: Pci_Address; Reg: Pci_Register; Field: Interfaces.Unsigned_32) return Interfaces.Unsigned_32;
   function Is_Field_Cleared(Addr: Pci_Address; Reg: Pci_Register; Field: Interfaces.Unsigned_32) return Boolean is (Read_Field(Addr, Reg, Field) = 0);
   procedure Set_Field(Addr: Pci_Address; Reg: Pci_Register; Field: Interfaces.Unsigned_32);

   BAR0_LOW: constant := 16#10#;
   BAR0_HIGH: constant := 16#14#;

   COMMAND: constant := 16#04#;
   COMMAND_MEMORY_ACCESS_ENABLE: constant := 2#01#;
   COMMAND_BUS_MASTER_ENABLE: constant := 2#10#;
   COMMAND_INTERRUPT_DISABLE: constant := 2#10_0000_0000#;

   DEVICESTATUS: constant := 16#AA#;
   DEVICESTATUS_TRANSACTIONPENDING: constant := 2#1_0000#;

   ID: constant := 16#00#;

   PMCSR: constant := 16#44#;
   PMCSR_POWER_STATE: constant := 2#11#;
end Ixgbe.Pci_Regs;
