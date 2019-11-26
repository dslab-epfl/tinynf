#!/bin/sh

THIS_DIR="$(dirname "$(readlink -f "$0")")"

if [ -z "$1" ]; then
  echo "[ERROR] Please provide the directory of the NF as the first argument to $0"
  exit 1
fi
NF_DIR="$(readlink -f "$1")"
NF_DIR_CLEAN="$(echo "$NF_DIR" | sed 's|/*$||' | sed 's|/|_|g')" # remove trailing slash, replace / by _

if [ -z "$2" ]; then
  echo "[ERROR] Please provide the kind as second argument to $0: 'custom', 'dpdk-shim', 'dpdk'"
  exit 1
fi
NF_KIND="$2"
case "$NF_KIND" in
  'custom')
    LTO_CHOICES='true false'
    PERIOD_CHOICES='2 4 8 16 32 64 128 256 512 1024'
    ONEWAY_CHOICES='true' # no reason not to since we're doing custom anyway
    ;;
  'dpdk-shim')
    LTO_CHOICES='true false'
    PERIOD_CHOICES='2 4 8 16 32 64 128 256 512 1024'
    ONEWAY_CHOICES='true false'
    export RTE_SDK="$THIS_DIR/../shims/dpdk"
    export RTE_TARGET='.'
    ;;
  'dpdk')
    LTO_CHOICES='false'
    PERIOD_CHOICES="NA"
    ONEWAY_CHOICES='false'
    ;;
  *)
    echo '[ERROR] Unknown kind'
    exit 1
    ;;
esac

if [ -z "$3" ]; then
  echo "[ERROR] Please provide the NF as third argument to $0"
  exit 1
fi
NF="$3"

# Necessary if DPDK has been used before and didn't exit cleanly
sudo rm -rf /dev/hugepages/*

cd "$THIS_DIR/../benchmarking"

# Pick the layer
LAYER=4
if [ "$NF" = 'bridge' ]; then LAYER=2; fi
if [ "$NF" = 'pol' ]; then LAYER=3; fi

# Bridge can't do one-way, by definition it may need to flood
# (even with only 2 devices, enabling one-way would be misleading)
if [ "$NF" = 'bridge' ]; then ONEWAY_CHOICES='false'; fi

# Vigor-specific
# Bridge needs double the standard capacity since it stores both input and output flows
if [ "$NF" = 'bridge' ]; then export CAPACITY=131072; fi
# Policer needs large maximums so as to not really police, since we measure throughput
if [ "$NF" = 'pol' ]; then export POLICER_BURST=10000000000; export POLICER_RATE=10000000000; fi

FILE_PREFIX="$THIS_DIR/$NF_DIR_CLEAN--$NF_KIND--$NF--"
rm -f "$FILE_PREFIX"*

for LTO in $LTO_CHOICES; do
  LTO_FLAG=''
  if [ "$LTO" = 'true' ]; then LTO_FLAG='-flto'; fi

  for ONEWAY in $ONEWAY_CHOICES; do
    SENDS=2
    ONEWAY_FLAG=''
    if [ "$ONEWAY" = 'true' ]; then SENDS=1; ONEWAY_FLAG="-DASSUME_ONE_WAY"; fi

    for PERIOD in $PERIOD_CHOICES; do
      # Bench kind is the only thing guaranteed to not need a recompilation (as long as the NF Makefile is smart), so let's do it in the inner loop
      for BENCH_KIND in throughput latency; do
        FILE="$FILE_PREFIX$BENCH_KIND.csv"

        TN_NF="$NF" TN_LDFLAGS="$LTO_FLAG" TN_CFLAGS="$LTO_FLAG $ONEWAY_FLAG -DIXGBE_PIPE_SCHEDULING_PERIOD=$PERIOD -DIXGBE_PIPE_MAX_SENDS=$SENDS" ./bench.sh "$NF_DIR" "$BENCH_KIND" "$LAYER"

        if [ ! -f "$FILE" ]; then
          printf "LTO,\tOneway,\tPeriod,\t%s\n" "$(head -n 1 bench.results)" > "$FILE"
        fi
        printf "%s,\t%s,\t%s,\t%s\n" "$LTO" "$ONEWAY" "$PERIOD" "$(tail -n +2 bench.results)" >> "$FILE"
        rm -f 'bench.results' # in case the next benchmark fails, it won't use these results by accident
      done
    done
  done
done
