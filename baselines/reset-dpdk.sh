#!/bin/sh
# Arguments: the PCI addresses that should be bound to DPDK

# Always make DPDK in case Linux got updated, reinstall the kernel module and re-bind the devices just to be sure
sudo rmmod igb_uio 2>/dev/null || true
make -C "$RTE_SDK" install -j$(nproc) T=x86_64-native-linuxapp-gcc DESTDIR=. >/dev/null 2>&1
sudo insmod "$RTE_SDK/$RTE_TARGET/kmod/igb_uio.ko"
sudo "$RTE_SDK/usertools/dpdk-devbind.py" -u $@ >/dev/null 2>&1
sudo "$RTE_SDK/usertools/dpdk-devbind.py" -b igb_uio $@
