#!/bin/sh

printf 'Tabulating results... This will take around 15 minutes due to the amount of data involved.\n\n'

RESULTS_DIR='results'

if [ ! -z "$1" ]; then
  RESULTS_DIR="$RESULTS_DIR-$1"
fi

round()
{
  # use sed to print 0.00 if the number is 0, and the leading zero if the number is >0 and <1
  echo "scale=2; $1 / 1" | bc | sed 's/^0$/0.00/' | sed 's/^\./0./'
}

med99()
{
  lines="$(cat "$1"/log* | wc -l)"
  num50="$(echo "$lines / 2" | bc)"
  num99="$(echo "$lines * 0.99 / 1" | bc)"
  # -S 50% allows sort to use up to half the machine's memory, which speeds it up a lot given the amount of data
  for n in $(cat "$1"/log* | awk "{print \$$2}" | sort -n -S 50% | sed "$num50"'p;'"$num99"'q;d' | tr '\n' ' '); do
    printf '%s\t' "$(round "$n")"
  done
}

printf '\tCycles\t\tInstrs\t\tL1 hits\t\tL2 hits\t\tL3 hits\n'
printf '\t50%%\t99%%\t50%%\t99%%\t50%%\t99%%\t50%%\t99%%\t50%%\t99%%\n'
for d in "$RESULTS_DIR"/*; do
  printf "$(basename "$d")\t"
  printf "$(med99 "$d" 1)"
  printf "$(med99 "$d" 2)"
  printf "$(med99 "$d" 3)"
  printf "$(med99 "$d" 4)"
  printf "$(med99 "$d" 5)\n"
done
