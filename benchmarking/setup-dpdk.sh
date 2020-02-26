#!/bin/sh
# Ensures that the devices given as $@, and only those devices, are bound to the DPDK kernel module

# Note that binding/unbinding devices occasionally has weird effects like killing SSH sessions,
# so we should only do it if absolutely necessary

# First, unbind all devices bound to DPDK, _without using DPDK_ since it may not be there
# (the user could not have DPDK, or have RTE_SDK set to our shim layer)
# notes about lspci:
# -D to force the domain even if there is only 1 (linux's driver unbind needs it)
# -mm to be machine-readable
# -vk to show all info including drivers
# 10 lines is enough to cover all info of a single device
for pci in $(lspci -Dmm | awk '{print $1}' | tr '\n' ' '); do
  driver="$(lspci -Dvmmk | grep "$pci" -A 10 | grep Driver | awk '{print $2}')"
  case "$driver" in
    igb_uio|vfio-pci|uio_pci_generic)
      echo -n "$pci" | sudo tee "/sys/bus/pci/devices/$pci/driver/unbind" >/dev/null 2>&1
      ;;
  esac
done

# Second, bind devices as needed - this time we can assume DPDK exists since otherwise we wouldn't be binding
# If this fails, reset: uninstall, recompile and reinstall the driver
needs_reset='false'
for pci in $@; do
  if ! sudo "$RTE_SDK/usertools/dpdk-devbind.py" --status | grep -F "$pci" | grep -q 'drv=igb_uio'; then
    if ! sudo "$RTE_SDK/usertools/dpdk-devbind.py" -b igb_uio "$pci" >/dev/null 2>&1; then
      needs_reset='true'
    fi
  fi
done

if [ "$needs_reset" = 'true' ]; then
  # Reset == uninstall driver, recompile, install driver
  # Unbind any devices still using the driver, otherwise we can't uninstall it
  for pci in $(sudo "$RTE_SDK/usertools/dpdk-devbind.py" --status | grep drv=igb_uio | awk '{ print $1 }'); do
    sudo "$RTE_SDK/usertools/dpdk-devbind.py" -u $pci
  done
  sudo rmmod igb_uio >/dev/null 2>&1 || true
  make -C "$RTE_SDK" install -j$(nproc) T=x86_64-native-linuxapp-gcc DESTDIR=. >/dev/null 2>&1
  sudo modprobe uio
  sudo insmod "$RTE_SDK/$RTE_TARGET/kmod/igb_uio.ko"
  sudo "$RTE_SDK/usertools/dpdk-devbind.py" -u $@ >/dev/null 2>&1
  sudo "$RTE_SDK/usertools/dpdk-devbind.py" -b igb_uio $@
fi
