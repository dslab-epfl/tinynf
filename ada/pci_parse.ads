with Environment;

package Pci_Parse is
  function Parse_Address(Str: in String) return Environment.Pci_Address;
end Pci_Parse;
