with Interfaces;

package Environment is
  generic type T is private;
  type T_Array is array(Integer range <>) of T;
  function Allocate(Count: in Integer) return T_Array;

  generic type T is private;
  type T_Access is access all T;
  function Get_Physical_Address(Value: T_Access) return Interfaces.Unsigned_64;

  generic type T is private;
  type T_Array is array(Integer range <>) of T;
  function Map_Physical_Memory(Addr: Integer; Count: Integer) return T_Array;

  type Pci_Bus is mod 2 ** 8;
  type Pci_Device is mod 2 ** 5;
  type Pci_Func is mod 2 ** 3;
  type Pci_Address is record
    Bus: Pci_Bus;
    Device: Pci_Device;
    Func: Pci_Func;
  end record;
  type Pci_Register is mod 2 ** 8;
  type Pci_Value is mod 2 ** 32;
  function Pci_Read(Addr: in Pci_Address; Reg: in Pci_Register) return Pci_Value;
  procedure Pci_Write(Addr: in Pci_Address; Reg: in Pci_Register; Value: in Pci_Value);
end Environment;
