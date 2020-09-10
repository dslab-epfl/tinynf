#!/bin/sh

echo 'Measuring low-level stats; this will take less than an hour...'

TINYNF_DIR='../../code'
DPDK_DIR='../baselines/dpdk/measurable-nop'
LAYER='2'
RESULTS_SUFFIX=''

if [ "$1" = 'policer' ]; then
  echo 'Using policer instead of NOP.'
  TINYNF_DIR='../baselines/policer/tinynf'
  DPDK_DIR='../baselines/policer/dpdk'
  LAYER='3'
  RESULTS_SUFFIX='-policer'
  export RTE_SDK="$(pwd)/../baselines/vigor/dpdk"
  export RTE_TARGET=x86_64-native-linuxapp-gcc
fi

# Ensure the papi submodule is cloned
git submodule update --init --recursive

# Get the absolute path to papi, we'll use it when building and running things from other dirs
PAPI_DIR="$(readlink -e papi)"

# Build papi if needed, but don't install it, we just want a local version
cd "$PAPI_DIR/src"
  if [ ! -e "libpapi.so" ]; then
    ./configure
    make
  fi
cd - >/dev/null

# Ensure papi can read events
echo 0 | sudo dd status=none of=/proc/sys/kernel/perf_event_paranoid

# Ensure the results folder is deleted so we don't accidentally end up with stale results
RESULTS_DIR="$(readlink -f results$RESULTS_SUFFIX)"
#rm -rf "$RESULTS_DIR"

# Ensure there are no leftover hugepages
sudo rm -rf /dev/hugepages/*

# Load the benchmark config
if [ -f ../../benchmarking/config ]; then
  . ../../benchmarking/config
else
  echo 'Please successfully run a benchmark at least once before running this'
  exit 1
fi

# Start a packet flood, waiting for it to have really started
ssh "$TESTER_HOST" "cd $REMOTE_FOLDER_NAME; ./bench-tester.sh flood $LAYER" >/dev/null 2>&1 &
sleep 30

# assumes pwd is right
# $1: result folder name, e.g. TinyNF or DPDK-1
run_nf()
{
  for i in $(seq 0 9); do
    # Remove output before the values themselves, and skip the first 1000 lines since they might have heatup effects
    LD_LIBRARY_PATH="$PAPI_DIR/src" TN_ARGS="$DUT_DEVS" taskset -c "$DUT_CPUS" make -f Makefile.benchmarking run 2>&1 | sed '0,/Counters:/d' | tail -n+1001 >"$RESULTS_DIR/$1/log$i"
  done
}

# Collect data on TinyNF
#cd "$TINYNF_DIR"
#  mkdir -p "$RESULTS_DIR/TinyNF"
#  TN_DEBUG=0 TN_CFLAGS="-DTN_DEBUG_PERF=10001000 -flto -s -I'$PAPI_DIR/src' -L'$PAPI_DIR/src' -lpapi" make -f Makefile.benchmarking build
#  run_nf 'TinyNF'
#cd - >/dev/null

# Collect data on DPDK, without and with batching
cd "$DPDK_DIR"
  for batch in 1 32; do
    mkdir -p "$RESULTS_DIR/DPDK-$batch"
    TN_BATCH_SIZE=$batch EXTRA_CFLAGS="-DTN_DEBUG_PERF=10001000 -I'$PAPI_DIR/src'" EXTRA_LDFLAGS="-L'$PAPI_DIR/src' -lpapi" make -f Makefile.benchmarking build >/dev/null 2>&1
    ../../../../benchmarking/bind-devices-to-uio.sh $DUT_DEVS
    run_nf "DPDK-$batch"
  done
cd - >/dev/null

# Stop the flood
ssh "$TESTER_HOST" "sudo pkill -9 MoonGen"
