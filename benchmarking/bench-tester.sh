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
  echo '[bench] Building MoonGen...'
  ./moongen/build.sh
fi

echo '[bench] Setting up tester...'

sudo rm -rf /dev/hugepages/* # make sure there are no leftovers from a previous run
sudo ./moongen/setup-hugetlbfs.sh

# code taken from libmoon's bind-interfaces-sh
sudo modprobe uio
(lsmod | grep igb_uio > /dev/null) || sudo insmod 'moongen/libmoon/deps/dpdk/x86_64-native-linuxapp-gcc/kmod/igb_uio.ko'

DPDK_DIR='moongen/libmoon/deps/dpdk'
for pci in "$TESTER_DEV_0" "$TESTER_DEV_1"; do
  if ! sudo "$DPDK_DIR/usertools/dpdk-devbind.py" --status | grep -F "$pci" | grep -q 'drv=igb_uio'; then
    sudo "$DPDK_DIR/usertools/dpdk-devbind.py" --force --bind igb_uio "$pci"
  fi
done

# Remove the output to avoid a stale one if the script fails
rm -f bench.result

# Ignore pointless DPDK output lines
echo '[bench] Running benchmark...'
sudo ./moongen/build/MoonGen bench-moongen.lua "$BENCH_TYPE" "$BENCH_LAYER" 2>&1 \
  | grep -v 'EAL: Detected [0-9]' \
  | grep -Fv 'EAL: No free hugepages reported in hugepages-1048576kB' \
  | grep -Fv 'EAL: Probing VFIO support...' \
  | grep -Fv 'EAL: PCI device' \
  | grep -Fv 'EAL:   probe driver:' \
  | grep -v '^   Device' \
  | grep -Fv 'PMD: ixgbe_dev_link_status_print' \
  | grep -Fv '[INFO]' \
  | grep -Fv '[WARN]  Error setting fdir filter: Invalid argument'
# that last one is a MoonGen bug when measuring latency multiple times in the same script; the latency results are still correct
