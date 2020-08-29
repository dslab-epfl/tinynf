#!/bin/sh

printf 'Tabulating results... This will take a few minutes due to the amount of data involved.\n\n'

round()
{
  # use sed to print 0.00 if the number is 0, and the leading zero if the number is >0 and <1
  echo "scale=2; $1 / 1" | bc | sed 's/^0$/0.00/' | sed 's/^\./0./'
}

medstd()
{
  for n in $(ministat -A -C $2 "$1" | tail -n 1 | awk '{print $5,$7}'); do
    printf "$(round $n)\t"
  done
}

printf '\tCycles\t\tInstrs\t\tL1 hits\t\tL2 hits\t\tL3 hits\n'
printf '\tmed\tstdev\tmed\tstdev\tmed\tstdev\tmed\tstdev\tmed\tstdev\n'
for f in results/*; do
  printf "$(basename "$f")\t"
  printf "$(medstd "$f" 1)"
  printf "$(medstd "$f" 2)"
  printf "$(medstd "$f" 3)"
  printf "$(medstd "$f" 4)"
  printf "$(medstd "$f" 5)\n"
done
