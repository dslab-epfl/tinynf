#!/bin/sh

echo 'Measuring low-level stats; this will take around an hour...'

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
RESULTS_DIR="$(readlink -f results)"
rm -rf "$RESULTS_DIR"

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
ssh "$TESTER_HOST" "cd $REMOTE_FOLDER_NAME; ./bench-tester.sh flood 2" >/dev/null 2>&1 &
sleep 30

# Collect data on TinyNF
cd ../../code
  mkdir -p "$RESULTS_DIR/TinyNF"
  TN_DEBUG=0 TN_CFLAGS="-DTN_DEBUG_PERF=10001000 -flto -s -I'$PAPI_DIR/src' -L'$PAPI_DIR/src' -lpapi" make -f Makefile.benchmarking build
  for i in $(seq 1 10); do
    LD_LIBRARY_PATH="$PAPI_DIR/src" TN_ARGS="$DUT_DEVS" taskset -c "$DUT_CPUS" make -f Makefile.benchmarking run >"$RESULTS_DIR/TinyNF/log$i" 2>&1
  done
cd - >/dev/null

# Collect data on DPDK
cd ../baselines/dpdk/measurable-nop
  for batch in 1 32; do
    mkdir -p "$RESULTS_DIR/DPDK-$batch"
    EXTRA_CFLAGS="-DBATCH_SIZE=$batch -DTN_DEBUG_PERF=10001000 -I'$PAPI_DIR/src'" EXTRA_LDFLAGS="-L'$PAPI_DIR/src' -lpapi" make -f Makefile.benchmarking build >/dev/null 2>&1
    ../../../../benchmarking/bind-devices-to-uio.sh $DUT_DEVS
    for i in $(seq 1 10); do
      LD_LIBRARY_PATH="$PAPI_DIR/src" taskset -c "$DUT_CPUS" make -f Makefile.benchmarking run >"$RESULTS_DIR/DPDK-$batch/log$i" 2>&1
    done
  done
cd - >/dev/null

# Stop the flood
ssh "$TESTER_HOST" "sudo pkill -9 MoonGen"
