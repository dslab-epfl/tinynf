#!/bin/sh

printf 'Tabulating results... This will take a few minutes due to the amount of data involved.\n\n'

avg()
{
	printf "%.3g" $(ministat -A -C $2 "$1" | tail -n 1 | awk '{print $6}')
}

medstd()
{
	printf "%.3g\t%.3g" $(ministat -A -C $2 "$1" | tail -n 1 | awk '{print $5,$7}')
}

printf '\tCycles\t\tInstrs\t\tL1d\tL2\tL3\n'
printf '\tmed\tstdev\tmed\tstdev\tavg\tavg\tavg\n'
for f in results/*; do
  printf "$(basename "$f")\t"
  printf "$(medstd "$f" 1)\t"
  printf "$(medstd "$f" 2)\t"
  printf "$(avg "$f" 3)\t"
  printf "$(avg "$f" 4)\t"
  printf "$(avg "$f" 5)\n"
done
