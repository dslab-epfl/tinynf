with Interfaces;

package Environment is
  generic type T is private;
  type T_Array is array(Integer range <>) of T;
  function Allocate(Count: in Integer) return T_Array;

  generic type T is private;
  type T_Access is access all T;
  function Get_Physical_Address(Value: T_Access) return Interfaces.Unsigned_64;
end Environment;
