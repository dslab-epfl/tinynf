with Interfaces;

package Environment is
  generic
    type T is private;
    type R is range <>;
    type T_Array is array(R) of T;
  function Allocate return T_Array;

  generic
    type T is private;
  function Get_Physical_Address(Value: access T) return Interfaces.Unsigned_64;

  generic
    type T is private;
    type R is range <>;
    type T_Array is array(R) of T;
  function Map_Physical_Memory(Addr: Integer) return T_Array;

  type Pci_Bus is mod 2 ** 8;
  type Pci_Device is mod 2 ** 5;
  type Pci_Func is mod 2 ** 3;
  type Pci_Address is record
    Bus: Pci_Bus;
    Device: Pci_Device;
    Func: Pci_Func;
  end record;
  type Pci_Register is mod 2 ** 8;
  function Pci_Read(Addr: in Pci_Address; Reg: in Pci_Register) return Interfaces.Unsigned_32;
  procedure Pci_Write(Addr: in Pci_Address; Reg: in Pci_Register; Value: in Interfaces.Unsigned_32);

  -- no "sleep" function here like in C; Ada has a built-in "delay" statement
end Environment;
