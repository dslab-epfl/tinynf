#!/bin/sh

if [ -z "$1" ]; then
  echo "[ERROR] Please provide the directory of the NF as the first argument to $0"
  exit 1
fi
NF_DIR="$1"
NF_DIR_CLEAN="$(echo "$NF_DIR" | sed 's|/*$||' | sed 's|/|_|g')" # remove trailing slash, replace / by _

THIS_DIR="$(pwd)"

cd ../benchmarking

for kind in throughput latency; do
  file="$THIS_DIR/$NF_DIR_CLEAN-$kind.results"
  rm -f "$file"

  for nf in nop nat fw pol bridge lb; do
    layer=4
    if [ "$nf" = 'bridge' ]; then layer=2; fi
    if [ "$nf" = 'pol' ]; then layer=3; fi

    for period in 1 2 4 8 16 32 64 128 256 512 1024; do
      ways='false true'
      if [ "$nf" = 'bridge' ]; then ways='false'; fi

      for oneway in $ways; do
        sends=2
        onewayflag=""
        if [ "$oneway" = 'true' ]; then sends=1; onewayflag="-DASSUME_ONE_WAY"; fi

        TN_NF="$nf" TN_CFLAGS="$onewayflag -DIXGBE_PIPE_SCHEDULING_PERIOD=$period -DIXGBE_PIPE_MAX_SENDS=$sends" ./bench.sh "$NF_DIR" "$kind" "$layer"

        if [ ! -f "$file" ]; then
          header="$(printf "nf,\tperiod,\toneway,\t%s\n" "$(head -n 1 bench.results)")"
        fi
        printf "%s,\t%s,\t%s,\t%s\n" "$nf" "$period" "$oneway" "$(tail -n +2 bench.results)" >> "$file"
      done
    done
  done
  sorted_file="$(cat $file | sort -V)" # -V sorts the numbers within the text in a human-friendly order
  echo "$header" > "$file"
  echo "$sorted_file" >> "$file"
done
