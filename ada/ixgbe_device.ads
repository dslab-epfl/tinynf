with Interfaces;

with Environment; use Environment;
with Ixgbe; use Ixgbe;

package Ixgbe_Device is
  type Dev is private;

  function Init_Device(Addr: in Pci_Address) return Dev;
  procedure Set_Promiscuous(Device: in out Dev);

private
  type Dev is record
    Buffer: Dev_Buffer;
    RX_Enabled: Boolean;
    TX_Enabled: Boolean;
  end record;
end Ixgbe_Device;
