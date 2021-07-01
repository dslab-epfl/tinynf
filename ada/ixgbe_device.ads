with Interfaces;

with Environment; use Environment;
with Ixgbe; use Ixgbe;

package Ixgbe_Device is
  type Dev is record
    Buffer: access Dev_Buffer;
    RX_Enabled: Boolean;
    TX_Enabled: Boolean;
  end record;

  function Init_Device(Addr: in Pci_Address) return Dev;
  procedure Set_Promiscuous(Device: in out Dev);
  function Set_Input(Device: not null access Dev; Ring: not null access Descriptor_Ring) return Register_Access;
  function Add_Output(Device: not null access Dev; Ring: not null access Descriptor_Ring; Head: not null access VolatileUInt32) return Register_Access;
end Ixgbe_Device;
