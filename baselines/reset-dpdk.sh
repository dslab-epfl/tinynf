#!/bin/sh
# Ensures that the devices given as $@ are bound to the DPDK kernel module

# Note that binding/unbinding devices occasionally has weird effects like killing SSH sessions,
# so we should only do it if absolutely necessary

needs_reset='false'
for pci in $@; do
  if ! sudo "$RTE_SDK/usertools/dpdk-devbind.py" --status | grep -F "$pci" | grep -q 'drv=igb_uio'; then
    needs_reset='true'
  fi
done

if [ "$needs_reset" = 'true' ]; then
  # Reset == uninstall driver, recompile, install driver
  # This also implies unbinding any devices that were using it, otherwise we can't uninstall it
  for pci in $(sudo "$RTE_SDK/usertools/dpdk-devbind.py" --status | grep drv=igb_uio | awk '{ print $1 }'); do
    sudo "$RTE_SDK/usertools/dpdk-devbind.py" -u $pci
  done
  sudo rmmod igb_uio || true
  make -C "$RTE_SDK" install -j$(nproc) T=x86_64-native-linuxapp-gcc DESTDIR=. >/dev/null 2>&1
  sudo modprobe uio
  sudo insmod "$RTE_SDK/$RTE_TARGET/kmod/igb_uio.ko"
  sudo "$RTE_SDK/usertools/dpdk-devbind.py" -u $@ >/dev/null 2>&1
  sudo "$RTE_SDK/usertools/dpdk-devbind.py" -b igb_uio $@
fi
