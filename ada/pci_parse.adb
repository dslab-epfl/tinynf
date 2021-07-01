package body Pci_Parse is
  function Parse_Address(Str: in String) return Environment.Pci_Address is
  begin
    return (Bus => Environment.Pci_Bus'Value("16#" & Str(Str'First .. Str'First+1) & "#"),
            Device => Environment.Pci_Device'Value("16#" & Str(Str'First+3 .. Str'First+4) & "#"),
            Func => Environment.Pci_Func'Value("16#" & Str(Str'First+6 .. Str'First+6) & "#"));
  end;
end Pci_Parse;
