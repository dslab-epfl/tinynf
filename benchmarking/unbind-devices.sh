#!/bin/sh
# Ensures that the devices given as $@, and only those devices, are not bound to any kernel driver
# Devices given as $@ may but do not need to have the domain (e.g. '83:00.0' and '0000:83:00.0' are equivalent assuming the domain is 0)

# List all PCI devices
# notes about lspci:
# -D to force the domain even if there is only 1 (linux's driver unbind needs it)
# -mm to be machine-readable
# -vk to show all info including drivers
# 10 lines is enough to cover all info of a single device
for pci in $(lspci -Dmm | awk '{print $1}' | tr '\n' ' '); do
  # Unbind if needed
  if [ ! -z "$(lspci -Dvmmk | grep -F "$pci" -A 10 | grep Driver | awk '{print $2}')" ]; then
    echo -n "$pci" | sudo tee "/sys/bus/pci/devices/$pci/driver/unbind" >/dev/null 2>&1
  fi
done
