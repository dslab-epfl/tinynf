with Interfaces;

with Environment; use Environment;
with Ixgbe; use Ixgbe;

package Ixgbe_Device is
  type Dev is private;

  function Init_Device(Addr: in Pci_Address) return Dev;
  procedure Set_Promiscuous(Device: in out Dev);
  function Set_Input(Device: not null access Dev; Ring: not null access Descriptor_Ring) return not null access VolatileUInt32;
  function Add_Output(Device: not null access Dev; Ring: not null access Descriptor_Ring; Head: not null access VolatileUInt32) return not null access VolatileUInt32;

private
  type Dev is record
    Buffer: Dev_Buffer;
    RX_Enabled: Boolean;
    TX_Enabled: Boolean;
  end record;
end Ixgbe_Device;
