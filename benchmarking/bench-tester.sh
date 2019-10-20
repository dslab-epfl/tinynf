#!/bin/sh

if [ -z "$1" ]; then
  echo "[ERROR] Please provide the type of benchmark as the first argument to $0"
  exit 1
fi
BENCH_TYPE="$1"

if [ -z "$2" ]; then
  echo "[ERROR] Please provide the layer of the benchmark as the second argument to $0"
  exit 1
fi
BENCH_LAYER="$2"

if [ ! -f config ]; then
  echo '[ERROR] There should be a "config" file next to this script...'
  exit 1
fi
. ./config

if [ ! -f moongen/build/MoonGen ]; then
  echo '[bench-tester] Building MoonGen...'
  ./moongen/build.sh
fi

echo '[bench-tester] Setting up hugepages...'
sudo ./moongen/setup-hugetlbfs.sh

echo '[bench-tester] Setting up the DPDK driver...'
# code taken from libmoon's bind-interfaces-sh
modprobe uio
(lsmod | grep igb_uio > /dev/null) || insmod 'moongen/libmoon/deps/dpdk/x86_64-native-linuxapp-gcc/kmod/igb_uio.ko'

echo '[bench-tester] Configuring interfaces...'
DPDK_DIR='moongen/libmoon/deps/dpdk'
for pci in "$TESTER_DEV_0" "$TESTER_DEV_1"; do
  if ! sudo "$DPDK_DIR/usertools/dpdk-devbind.py" --status | grep -F "$pci" | grep -q 'drv=igb_uio'; then
    sudo "$DPDK_DIR/usertools/dpdk-devbind.py" --force --bind igb_uio "$pci"
  fi
done

echo '[bench-tester] Running...'
sudo ./moongen/build/MoonGen bench-moongen.lua "$BENCH_TYPE" "$BENCH_LAYER"
