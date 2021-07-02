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
  ./moongen/libmoon/build.sh --moongen
  echo '[bench] Ignore Git reporting bad submodule paths, the script initializes submodules beforehand so this is irrelevant'
  echo '[bench] Ignore errors after "Trying to bind interfaces" above, the binding is not supposed to work at that point'
fi

echo '[bench] Setting up tester...'

# Make sure there are no leftover MoonGen processes
sudo pkill -9 MoonGen
# Make sure there are no leftovers from a previous run
sudo rm -rf /dev/hugepages/*

./bind-devices-to-uio.sh $TESTER_DEVS

# Remove the output to avoid a stale one if the script fails
rm -f bench.result

CROSS_OPT=
if [ $TESTER_CABLES_CROSSED -ne 0 ]; then
  CROSS_OPT='-x'
fi

echo '[bench] Running benchmark...'
# Ignore pointless output (this is why this script needs -o pipefail)
taskset -c $TESTER_CPUS sudo ./moongen/build/MoonGen bench-moongen.lua $CROSS_OPT "$@" 2>&1 \
  | grep -Fv --line-buffered 'EAL: Detected' \
  | grep -Fv --line-buffered 'EAL: No free hugepages reported in hugepages-1048576kB' \
  | grep -Fv --line-buffered 'EAL: Probing VFIO support...' \
  | grep -Fv --line-buffered 'EAL: VFIO support initialized' \
  | grep -Fv --line-buffered 'EAL: PCI device' \
  | grep -Fv --line-buffered 'EAL:   probe driver:' \
  | grep -Fv --line-buffered 'EAL:   using IOMMU' \
  | grep -Fv --line-buffered 'EAL: Ignore mapping IO port' \
  | grep  -v --line-buffered '^   Device' \
  | grep -Fv --line-buffered 'PMD: ixgbe_dev_link_status_print' \
  | grep -Fv --line-buffered '[INFO]'
