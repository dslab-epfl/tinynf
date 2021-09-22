with System.Storage_Elements;

package Ixgbe_Constants is
  Packet_Buffer_Size: constant := 2 ** 11;
  Ring_Size: constant := 2 ** 8;
  Flush_Period: constant := 8;
  Recycle_Period: constant := 64;

  type Packet_Buffer_Length is mod Ixgbe_Constants.Packet_Buffer_Size;
  type Packet_Data is array(Packet_Buffer_Length) of System.Storage_Elements.Storage_Element;
end Ixgbe_Constants;
