#!/bin/sh

printf 'Tabulating results... This will take over half an hour due to the amount of data involved.\n\n'

# Assuming there are log1..log10 files each containing 10001000 entries in $1, merges them into a 'logsorted' file,
# discarding the worst 0.01% entries in terms of cycles of each log since they're weird outliers probably caused by some CPU weirdness
merge_logs()
{
  rm -f "$1/logsorted"
  for i in $(seq 1 10); do
    sed -e '0,/Counters:/d' "$1/log$i" | sort -n | head -n+10000000 >> "$1/logsorted"
  done
}

round()
{
  # use sed to print 0.00 if the number is 0, and the leading zero if the number is >0 and <1
  echo "scale=2; $1 / 1" | bc | sed 's/^0$/0.00/' | sed 's/^\./0./'
}

medstd()
{
  for n in $(ministat -A -C $2 "$1/logsorted" | tail -n 1 | awk '{print $5,$7}'); do
    printf "$(round $n)\t"
  done
}

printf '\tCycles\t\tInstrs\t\tL1 hits\t\tL2 hits\t\tL3 hits\n'
printf '\tmed\tstdev\tmed\tstdev\tmed\tstdev\tmed\tstdev\tmed\tstdev\n'
for d in results/*; do
  printf "$(basename "$d")\t"
  merge_logs "$d"
  printf "$(medstd "$d" 1)"
  printf "$(medstd "$d" 2)"
  printf "$(medstd "$d" 3)"
  printf "$(medstd "$d" 4)"
  printf "$(medstd "$d" 5)\n"
done
