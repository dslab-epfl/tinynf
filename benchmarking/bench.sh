#!/bin/sh
# Parameters: <NF directory> <bench type (latency/throughput)> <layer of flows in bench>
# Builds the NF using 'make' then runs it with 'make run' passing the PCI devices as '$TN_ARGS'
# Exits with a non-zero code if the benchmark fails for any reason.
# Overrideable behavior:
# - The NF process name defaults to 'tinynf', but will be the value printed out by 'make print-nf-name' if this task exists

LOG_FILE='bench.log'

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

echo '[bench] Setting up the benchmark...'

# Ensure there are no outdated (and thus misleading) results/logs
rm -rf results *.log

# Get NF name, as explained in the script header
make -C "$NF_DIR" -q print-nf-name >/dev/null 2>&1
if [ $? -eq 2 ]; then
  NF_NAME=tinynf # no print-nf-name task, use default
else
  NF_NAME="$(make -C "$NF_DIR" -s print-nf-name)" # -s to not print 'Entering directory...'
fi

# Kill the NF in case some old instance is still running
sudo pkill -9 "$NF_NAME" >/dev/null 2>&1

THIS_DIR="$(dirname "$(readlink -f "$0")")"

if [ ! -f "$THIS_DIR/config" ]; then
  echo "[ERROR] Please create a 'config' file from the 'config.template' file in the same directory as $0"
  exit 1
fi
. "$THIS_DIR/config"


git submodule update --init --recursive
if [ $? -ne 0 ]; then
  echo '[FATAL] Could not update submodules'
  exit 1
fi

rsync -a -q . "$TESTER_HOST:tinynf-benchmarking"
if [ $? -ne 0 ]; then
  echo '[FATAL] Could not copy scripts'
  exit 1
fi

echo '[bench] Building and running the NF...'

TN_ARGS="$MB_DEV_0 $MB_DEV_1" make -C "$NF_DIR" >"$LOG_FILE" 2>&1
if [ $? -ne 0 ]; then
  echo "[FATAL] Could not build; the $LOG_FILE file in the same directory as $0 may be useful"
  exit 1
fi

TN_ARGS="$MB_DEV_0 $MB_DEV_1" taskset -c "$MB_CPU" make -C "$NF_DIR" run >>"$LOG_FILE" 2>&1 &
# Sleep (as little as possible) if the NF needs a while to start
for i in $(seq 1 30); do
  sleep 1
  NF_PID="$(pgrep -x "$NF_NAME")"
  if [ ! -z "$NF_PID" ]; then
    break
  fi
done
if [ -z "$NF_PID" ]; then
  echo "[FATAL] Could not launch the NF; the $LOG_FILE file in the same directory as $0 may be useful"
  exit 1
fi

ssh "$TESTER_HOST" "cd tinynf-benchmarking; ./bench-tester.sh $BENCH_TYPE $BENCH_LAYER"
if [ $? -eq 0 ]; then
  scp -r "$TESTER_HOST"':tinynf-benchmarking/results' . >/dev/null 2>&1
  if [ $? -eq 0 ]; then
    echo "[bench] Done! Results are in the results/ folder, and the log in $LOG_FILE, in the same directory as $0"
    RESULT=0
  else
    echo '[FATAL] Could not fetch result'
    RESULT=1
  fi
else
  echo '[FATAL] Run failed'
  RESULT=1
fi

# Ensure we always kill the NF at the end, even in cases of failure
sudo kill -9 "$NF_PID" >/dev/null 2>&1

exit $RESULT
