#!/bin/sh
# Parameters: <NF directory> <bench type (latency/throughput)> <layer of flows in bench>
# Builds the NF using 'make' then runs it with 'make run' passing the PCI devices as '$TN_ARGS'
# Overrideable variables:
# - NF_NAME, defaults to 'tinynf', the process name of the NF (used to check if it's alive and kill it later)

if [ -z "$NF_NAME" ]; then
  NF_NAME='tinynf'
fi
LOG_FILE='bench.log'
RESULTS_FILE='bench.results'

if [ -z "$1" ]; then
  echo "[ERROR] Please provide the directory of the NF as the first argument to $0"
  exit 1
fi
NF_DIR="$1"

if [ -z "$2" ]; then
  echo "[ERROR] Please provide the type of benchmark as the second argument to $0"
  exit 1
fi
BENCH_TYPE="$2"

if [ -z "$3" ]; then
  echo "[ERROR] Please provide the layer of the benchmark as the third argument to $0"
  exit 1
fi
BENCH_LAYER="$3"

if [ ! -z "$(pgrep -x "$NF_NAME")" ]; then
  echo '[ERROR] The NF is already running'
  exit 1
fi

THIS_DIR="$(dirname "$(readlink -f "$0")")"

if [ ! -f "$THIS_DIR/config" ]; then
  echo "[ERROR] Please create a 'config' file from the 'config.template' file in the same directory as $0"
  exit 1
fi
. "$THIS_DIR/config"

echo '[bench] Cloning submodules...'
git submodule update --init --recursive

echo '[bench] Copying scripts on tester...'
rsync -a -q --exclude '*.log' --exclude '*.results' . "$TESTER_HOST:tinynf-benchmarking"

echo '[bench] Building NF...'
TN_ARGS="$MB_DEV_0 $MB_DEV_1" make -C "$NF_DIR" >"$LOG_FILE" 2>&1

echo '[bench] Running NF...'
TN_ARGS="$MB_DEV_0 $MB_DEV_1" taskset -c "$MB_CPU" make -C "$NF_DIR" run >>"$LOG_FILE" 2>&1 &

# Sleep for as much as 20 seconds if the NF needs a while to start, but as little as possible
for i in $(seq 1 20); do
  sleep 1
  NF_PID="$(pgrep -x "$NF_NAME")"
  if [ ! -z "$NF_PID" ]; then
    break
  fi
done
if [ -z "$NF_PID" ]; then
  echo "[ERROR] Could not launch the NF. The $LOG_FILE file in the same directory as $0 may be useful"
  cat "$LOG_FILE"
  exit 1
fi

echo '[bench] Running benchmark on tester...'
ssh "$TESTER_HOST" "cd tinynf-benchmarking; ./bench-tester.sh $BENCH_TYPE $BENCH_LAYER"

echo '[bench] Fetching results...'
scp "$TESTER_HOST:tinynf-benchmarking/results.csv" "$RESULTS_FILE"

echo '[bench] Stopping NF...'
sudo kill -9 "$NF_PID" >/dev/null 2>&1

echo "[bench] Done! Results are in $RESULTS_FILE, and the log in $LOG_FILE, in the same directory as $0"
