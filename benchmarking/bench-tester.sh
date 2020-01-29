#!/bin/bash
# Bash-only feature; doing it the POSIX-compliant way requires a FIFO, which complicates lifetime tracking enormously
set -o pipefail

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
  echo '[bench] Ignore errors after "Trying to bind interfaces" above, the binding is not supposed to work at that point'
fi

echo '[bench] Setting up tester...'

sudo pkill -x -9 MoonGen >/dev/null 2>&1 # in case it crashed previously
sudo rm -rf /dev/hugepages/* # make sure there are no leftovers from a previous run

RTE_SDK='moongen/libmoon/deps/dpdk' RTE_TARGET='x86_64-native-linuxapp-gcc' ./setup-dpdk.sh "$TESTER_DEV_0" "$TESTER_DEV_1"

# Remove the output to avoid a stale one if the script fails
rm -f bench.result

echo '[bench] Running benchmark...'
# Ignore pointless output (this is why this script needs -o pipefail)
sudo ./moongen/build/MoonGen bench-moongen.lua "$BENCH_TYPE" "$BENCH_LAYER" 2>&1 \
  | grep -Fv --line-buffered 'EAL: Detected' \
  | grep -Fv --line-buffered 'EAL: No free hugepages reported in hugepages-1048576kB' \
  | grep -Fv --line-buffered 'EAL: Probing VFIO support...' \
  | grep -Fv --line-buffered 'EAL: PCI device' \
  | grep -Fv --line-buffered 'EAL:   probe driver:' \
  | grep  -v --line-buffered '^   Device' \
  | grep -Fv --line-buffered 'PMD: ixgbe_dev_link_status_print' \
  | grep -Fv --line-buffered '[INFO]'
