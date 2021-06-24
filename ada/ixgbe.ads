with Interfaces;

package Ixgbe is
  subtype UInt32 is Interfaces.Unsigned_32;
  subtype Int64 is Interfaces.Integer_64;

  type Descriptor is record
    Buffer: Int64;
    Metadata: Int64;
  end record
  with Pack;

  type TransmitHead is record
    Value: UInt32;
  end record;
  for TransmitHead'Alignment use 64; -- full cache line to avoid contention
end Ixgbe;
