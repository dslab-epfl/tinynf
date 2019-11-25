#!/bin/sh
# Completely reset the state of the DPDK kernel module: uninstall, recompile, install
# Arguments: the PCI addresses that should be bound to DPDK

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
