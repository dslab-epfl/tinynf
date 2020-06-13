#!/bin/sh
# Ensures that the devices given as $@, and only those devices, are not bound to any kernel driver
# Devices given as $@ may but do not need to have the domain (e.g. '83:00.0' and '0000:83:00.0' are equivalent assuming the domain is 0)

# see bind-devices script for an explanation of lspci parameters and overall logic
for pci in $(lspci -mm | cut -d ' ' -f 1 | tr '\n' ' '); do
  if echo "$@" | grep -Fq "$pci" ; then
    if [ ! -z "$(lspci -vmmk | grep -F "$pci" -A 10 | grep Driver | cut -f 2)" ]; then
      full_pci="$(lspci -D | grep -F "$pci" | cut -d ' ' -f 1)"
      echo -n "$full_pci" | sudo tee "/sys/bus/pci/devices/$full_pci/driver/unbind" >/dev/null 2>&1
    fi
  fi
done
