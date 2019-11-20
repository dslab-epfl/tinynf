#!/bin/sh
set -x

if [ -z "$1" ]; then
  echo "[ERROR] Please provide the directory of the NF as the first argument to $0"
  exit 1
fi
NF_DIR="$1"
NF_DIR_CLEAN="$(echo "$NF_DIR" | sed 's|/*$||' | sed 's|/|_|g')" # remove trailing slash, replace / by _

# just in case (especially if someone has been using DPDK...)
sudo rm -rf /dev/hugepages/*

THIS_DIR="$(pwd)"

cd ../benchmarking

for kind in throughput latency; do
  file="$THIS_DIR/$NF_DIR_CLEAN-$kind.csv"
  rm -f "$file"

  for nf in nop nat fw pol bridge; do
    layer=4
    if [ "$nf" = 'bridge' ]; then layer=2; fi
    if [ "$nf" = 'pol' ]; then layer=3; fi

    for lto in 'false' 'true'; do
      ltoflag=''
      if [ "$lto" = 'true' ]; then ltoflag='-flto'; fi

      for period in 32; do #1 2 4 8 16 32 64 128 256 512 1024; do
        ways='false true'
        if [ "$nf" = 'bridge' ]; then ways='false'; fi

        for oneway in $ways; do
          sends=2
          onewayflag=''
          if [ "$oneway" = 'true' ]; then sends=1; onewayflag="-DASSUME_ONE_WAY"; fi

          TN_NF="$nf" TN_LDFLAGS="$ltoflag" TN_CFLAGS=" $ltoflag $onewayflag -DIXGBE_PIPE_SCHEDULING_PERIOD=$period -DIXGBE_PIPE_MAX_SENDS=$sends" ./bench.sh "$NF_DIR" "$kind" "$layer"

          if [ ! -f "$file" ]; then
            header="$(printf "nf,\tLTO,\tperiod,\toneway,\t%s\n" "$(head -n 1 bench.results)")"
          fi
          printf "%s,\t%s,\t%s,\t%s,\t%s\n" "$nf" "$lto" "$period" "$oneway" "$(tail -n +2 bench.results)" >> "$file"
          rm -f 'bench.results' # in case the next benchmark fails, it won't use these results by accident
        done
      done
    done
  done
  sorted_file="$(cat $file | sort -V)" # -V sorts the numbers within the text in a human-friendly order
  echo "$header" > "$file"
  echo "$sorted_file" >> "$file"
done
