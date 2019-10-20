#!/bin/sh

LOG_FILE='bench.log'
RESULTS_FILE='bench.results'

if [ -z "$1" ]; then
  echo "[ERROR] Please provide the directory of the NF as the first argument to $0"
  exit 1
fi
NF_DIR="$1"

if [ -z "$2" ]; then
  echo "[ERROR] Please provide the type of benchmark as the first argument to $0"
  exit 1
fi
BENCH_TYPE="$2"

echo '[bench] Loading config...'
if [ ! -f config.sh ]; then
  echo '[ERROR] Please create a benchmarking/config.sh file from benchmarking/config.sh.template'
  exit 1
fi
. config.sh

echo '[bench] Cloning submodules...'
git submodule update --init --recursive

echo '[bench] Copying scripts on tester...'
rsync -a -q --exclude '*.log' --exclude '*.results' . "$TESTER_HOST:tinynf-benchmarking"

echo '[bench] Building NF...'
make -C "$NF_DIR"

echo '[bench] Running NF...'
sudo taskset -c "$MB_CPU" tinynf "$MB_DEV_0" "$MB_DEV_1" 2>&1 >"$LOG_FILE" &
NF_PID=$!
if ! kill -0 "$NF_PID" 2> /dev/null; then
  echo "[ERROR] Could not launch the NF. The $LOG_FILE file in the same directory as $0 may be useful"
  exit 1
fi

echo '[bench] Running benchmark on tester...'
ssh "$TESTER_HOST" 'cd tinynf-benchmarking; ./bench-tester.sh $BENCH_TYPE'

echo '[bench] Fetching results...'
scp "$TESTER_HOST:tinynf-benchmarking/results.csv" "$RESULTS_FILE"

echo '[bench] Stopping NF...'
kill -9 tinynf 2>&1 >/dev/null

echo "[bench] Done! Results are in $RESULTS_FILE, and the log in $LOG_FILE, in the same directory as $0"
