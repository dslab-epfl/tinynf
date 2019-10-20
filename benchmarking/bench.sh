#!/bin/sh

NF_FILE='tinynf'
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

if [ ! -z "$(pgrep "$NF_FILE")" ]; then
  echo '[ERROR] The NF is already running'
  exit 1
fi

if [ ! -f config ]; then
  echo "[ERROR] Please create a 'config' file from the 'config.template' file in the same directory as $0"
  exit 1
fi
. ./config

echo '[bench] Cloning submodules...'
git submodule update --init --recursive

echo '[bench] Copying scripts on tester...'
rsync -a -q --exclude '*.log' --exclude '*.results' . "$TESTER_HOST:tinynf-benchmarking"

echo '[bench] Building NF...'
make -C "$NF_DIR" >/dev/null

echo '[bench] Running NF...'
sudo taskset -c "$MB_CPU" "$NF_DIR"/"$NF_FILE" "$MB_DEV_0" "$MB_DEV_1" >"$LOG_FILE" 2>&1 &
sleep 1 # so that the NF has time to fail if needed
NF_PID=$(pgrep "$NF_FILE")
if [ -z "$NF_PID" ]; then
  echo "[ERROR] Could not launch the NF. The $LOG_FILE file in the same directory as $0 may be useful"
  exit 1
fi

echo '[bench] Running benchmark on tester...'
ssh "$TESTER_HOST" "cd tinynf-benchmarking; ./bench-tester.sh $BENCH_TYPE $BENCH_LAYER"

echo '[bench] Fetching results...'
scp "$TESTER_HOST:tinynf-benchmarking/results.csv" "$RESULTS_FILE"

echo '[bench] Stopping NF...'
sudo kill -9 "$NF_PID" >/dev/null 2>&1

echo "[bench] Done! Results are in $RESULTS_FILE, and the log in $LOG_FILE, in the same directory as $0"
