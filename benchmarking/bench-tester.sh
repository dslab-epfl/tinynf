#!/bin/bash
# Bash-only feature; doing it the POSIX-compliant way requires a FIFO, which complicates lifetime tracking enormously
set -o pipefail

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

RTE_SDK='moongen/libmoon/deps/dpdk' RTE_TARGET='x86_64-native-linuxapp-gcc' ./setup-dpdk.sh $TESTER_DEVS

# Remove the output to avoid a stale one if the script fails
rm -f bench.result

CROSS_OPT=
if [ $TESTER_CABLES_CROSSED -ne 0 ]; then
  CROSS_OPT='-x'
fi

echo '[bench] Running benchmark...'
# Ignore pointless output (this is why this script needs -o pipefail)
sudo ./moongen/build/MoonGen bench-moongen.lua $CROSS_OPT "$@" 2>&1 \
  | grep -Fv --line-buffered 'EAL: Detected' \
  | grep -Fv --line-buffered 'EAL: No free hugepages reported in hugepages-1048576kB' \
  | grep -Fv --line-buffered 'EAL: Probing VFIO support...' \
  | grep -Fv --line-buffered 'EAL: PCI device' \
  | grep -Fv --line-buffered 'EAL:   probe driver:' \
  | grep  -v --line-buffered '^   Device' \
  | grep -Fv --line-buffered 'PMD: ixgbe_dev_link_status_print' \
  | grep -Fv --line-buffered '[INFO]'
