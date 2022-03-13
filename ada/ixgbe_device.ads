with Interfaces;
with System;

with Environment; use Environment;
with Ixgbe; use Ixgbe;

package Ixgbe_Device is
  type Device is record
    Buffer: not null access Device_Buffer;
    RX_Enabled: Boolean;
    TX_Enabled: Boolean;
  end record;

  type Descriptor is record
    Addr: Interfaces.Unsigned_64;
    Metadata: Interfaces.Unsigned_64;
  end record
    with Pack,
         Volatile;

  Packet_Buffer_Size: constant := 2 ** 11;
  type Packet_Buffer_Length is mod Packet_Buffer_Size;
  type Packet_Data is array(Packet_Buffer_Length) of Interfaces.Unsigned_8
       with Volatile;

  type Transmit_Head is record
    Value: aliased Interfaces.Unsigned_32;
  end record
    with Size => 64*8,
         Alignment => 64,
         Bit_Order => System.Low_Order_First,
         Volatile;
  for Transmit_Head use record
    Value at 0 range 0 .. 31;
  end record;

  Ring_Size: constant := 2 ** 8;
  type Delimiter_Range is mod Ring_Size;
  type Descriptor_Ring is array(Delimiter_Range) of aliased Descriptor;

  FiveTuple_Filters_Count: constant := 128;
  Interrupt_Registers_Count: constant := 3;
  Multicast_Table_Array_Size: constant := 4 * 1024;
  Pools_Count: constant := 64;
  Receive_Addresses_Count: constant := 128;
  Receive_Queues_Count: constant := 128;
  Transmit_Queues_Count: constant := 128;
  Traffic_Classes_Count: constant := 8;
  Unicast_Table_Array_Size: constant := 4 * 1024;

  function Init_Device(Addr: in Pci_Address) return Device;
  procedure Set_Promiscuous(Dev: in out Device);
  function Set_Input(Dev: in out Device; Ring: not null access Descriptor_Ring) return Register_Access;
  function Add_Output(Dev: in out Device; Ring: not null access Descriptor_Ring; Head: not null access Transmit_Head) return Register_Access;

private
  function After_Timeout(Timeout: Duration; Cleared: Boolean; Buffer: access Device_Buffer; Reg: in Interfaces.Unsigned_32; Field: in Interfaces.Unsigned_32) return Boolean;
end Ixgbe_Device;
