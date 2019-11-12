sudo pkill -9 click # we shouldn't need this but in case it errored...

resultsdir="$(pwd)"

cd ../benchmarking

for nf in nop nat fw pol bridge lb; do
  layer=4
  if [ "$nf" = 'bridge' ]; then layer=2; fi
  if [ "$nf" = 'pol' ]; then layer=3; fi

  for kind in throughput latency; do
    file="$resultsdir/click-$nf-$kind.results"
    rm -f "$file"

    for period in 1 2 4 8 16 32 64 128 256 512 1024; do
      ways='false true'
      if [ "$nf" = 'bridge' ]; then ways='false'; fi

      for oneway in $ways; do
        sends=2
        if [ "$oneway" = 'true' ]; then sends=1; fi

        TN_CLICK_NF=$nf CFLAGS="-DASSUME_ONE_WAY=$oneway -DIXGBE_PIPE_SCHEDULING_PERIOD=$period -DIXGBE_PIPE_MAX_SENDS=$sends" ./bench.sh ~/tinynf/baselines/click $kind $layer

        if [ ! -f "$file" ]; then
          printf "period,\toneway,\t%s\n" "$(head -n 1 bench.results)" > "$file"
        fi
        printf "%s,\t%s,\t%s\n" "$period" "$oneway" "$(tail -n +2 bench.results)" >> "$file"
      done
    done
  done
done
