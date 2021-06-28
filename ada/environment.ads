package Environment is
  generic type T is private;
  type T_Array is array(Integer range <>) of T;

  function Allocate(Count: in Integer) return T_Array;
end Environment;
