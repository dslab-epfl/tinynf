#!/bin/sh

# Assuming there are log1..log10 files each containing 10001000 entries, merges them into a 'logsorted' file,
# discarding the worst 0.01% entries in terms of cycles of each log since they're weird outliers probably caused by some CPU weirdness
merge_logs()
{
  rm -f logsorted
  for i in $(seq 1 10); do
    sed -e '0,/Counters:/d' log$i | sort -n | head -n+10000000 >> logsorted
  done
}

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

# Get the results folder, creating it if needed
mkdir -p results
RESULTS_DIR="$(readlink -e results)"

# Ensure there are no leftover hugepages
sudo rm -rf /dev/hugepages/*

# Load the benchmark config
if [ -f ../../benchmarking/config ]; then
  . ../../benchmarking/config
else
  echo 'Please successfully run a benchmark at least once before running this'
  exit 1
fi

# Start a packet flood
ssh "$TESTER_HOST" "cd $REMOTE_FOLDER_NAME; ./bench-tester.sh flood 2" >/dev/null 2>&1 &

# Collect data on TinyNF
cd ../../code
  TN_DEBUG=0 TN_CFLAGS="-DTN_DEBUG_PERF=10001000 -flto -s -I '$PAPI_DIR/src' -L '$PAPI_DIR/src' -lpapi" make
  for i in $(seq 1 10); do
    sudo LD_LIBRARY_PATH="$PAPI_DIR/src" taskset -c "$DUT_CPUS" ./tinynf $DUT_DEVS >log$i 2>&1
  done
  merge_logs
  mv logsorted "$RESULTS_DIR/tinynf"
cd - >/dev/null

# Collect data on DPDK
#cd ../../baselines/dpdk/measurable-nop
#  for batch in 1 32; do
#    EXTRA_CFLAGS="-DBATCH_SIZE=$batch -DTN_DEBUG_PERF=10001000 -I '$PAPI_DIR/src'" EXTRA_LDFLAGS="-L '$PAPI_DIR/src' -lpapi" make
#    merge_logs
#  done
#cd -

# Stop the flood
ssh "$TESTER_HOST" "sudo pkill -9 MoonGen"
