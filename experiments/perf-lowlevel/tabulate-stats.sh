#!/bin/sh

printf 'Tabulating results... This will take around 10 minutes due to the amount of data involved.\n\n'

round()
{
  # use sed to print 0.00 if the number is 0, and the leading zero if the number is >0 and <1
  echo "scale=2; $1 / 1" | bc | sed 's/^0$/0.00/' | sed 's/^\./0./'
}

medstd()
{
  for n in $(cat "$1"/log* | ministat -A -C $2 | tail -n 1 | awk '{print $5,$7}'); do
    printf "$(round $n)\t"
  done
}

printf '\tCycles\t\tInstrs\t\tL1 hits\t\tL2 hits\t\tL3 hits\n'
printf '\tmed\tstdev\tmed\tstdev\tmed\tstdev\tmed\tstdev\tmed\tstdev\n'
for d in results/*; do
  printf "$(basename "$d")\t"
  printf "$(medstd "$d" 1)"
  printf "$(medstd "$d" 2)"
  printf "$(medstd "$d" 3)"
  printf "$(medstd "$d" 4)"
  printf "$(medstd "$d" 5)\n"
done
