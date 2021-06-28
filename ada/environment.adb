with Ada.Unchecked_Conversion;
with System; use System;
with System.Storage_Elements; use System.Storage_Elements;
with Interfaces.C;
with GNAT.OS_Lib;

package body Environment is
  -- void *mmap(void *addr, size_t length, int prot, int flags, int fd, off_t offset);
  function Mmap(addr: Address;
                length: Interfaces.C.size_t;
                prot: Interfaces.C.int;
                flags: Interfaces.C.int;
                fd: Interfaces.C.int;
                offset: Interfaces.C.long) return Address
    with Import => True,
         Convention => C,
         External_Name => "mmap";

  Huge_Page_Size: constant := 2 ** 30; -- 1 GB

  type Flags is mod Interfaces.C.int'Last;
  PROT_READ: constant Flags := 1;
  PROT_WRITE: constant Flags := 2;
  MAP_SHARED: constant Flags := 16#1#;
  MAP_ANONYMOUS: constant Flags := 16#20#;
  MAP_POPULATE: constant Flags := 16#8000#;
  MAP_HUGETLB: constant Flags := 16#40000#;
  MAP_HUGE_1GB: constant Flags := 16#78000000#; -- Huge_Page_Size << 26

  Allocator_Page: Address := Mmap(Null_Address,
                                  Huge_Page_Size,
                                  Interfaces.C.int(PROT_READ or PROT_WRITE),
                                  Interfaces.C.int(MAP_HUGETLB or MAP_HUGE_1GB or MAP_ANONYMOUS or MAP_SHARED or MAP_POPULATE),
                                  Interfaces.C.int(-1),
                                  Interfaces.C.long(0));
  Allocator_Used_Bytes: Storage_Offset := 0;

  function Allocate(Count: in Integer) return T_Array is
    Align_Diff: Storage_Offset;
  begin
    if Allocator_Page = To_Address(-1) then -- MAP_FAILED
      GNAT.OS_Lib.OS_Exit(1);
    end if;

    -- Note that Ada's 'Size is in bits!

    Align_Diff := Allocator_Used_Bytes rem (T'Size*8 + 64 - (T'Size*8 rem 64));
    Allocator_Page := Allocator_Page + Align_Diff;
    Allocator_Used_Bytes := Allocator_Used_Bytes + Align_Diff;

    declare
      Result: T_Array(0.. Count - 1);
      for Result'Address use Allocator_Page;
    begin
      Allocator_Page := Allocator_Page + Storage_Offset(Count * T'Size*8);
      Allocator_Used_Bytes := Allocator_Used_bytes + Storage_Offset(Count * T'Size*8);
      return Result;
    end;
  end;
end Environment;
