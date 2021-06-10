#!/bin/sh

printf 'Tabulating results... This will take around 10min due to the amount of data involved.\n\n'

round()
{
  digits=3
  # we only need 2 decimal places after the dot, no point in being more precise than that
  if echo "$1" | grep -q '^0\.' ; then
    digits=2
  fi
  # round to 3 significant digits, replace exponential notation by an actual exponent
  full="$(printf '%.'"$digits"'g' "$1" | sed 's/e+/e/' | sed 's/e/*10^/')"
  # compute said exponent, rounding to 2 digits after the decimal point
  echo "scale=2; $full / 1" | bc
}

med99()
{
  lines="$(cat "$1"/log* | wc -l)"
  num50="$(echo "$lines / 2 + 1" | bc)p;"
  if [ -z "$3" ]; then
    num99="$(echo "$lines * 0.99 / 1" | bc)q;"
  else
    num99='' # don't show 99th if there is a 3rd arg, for IPC
  fi
  # -S 50% allows sort to use up to half the machine's memory, which speeds it up a lot given the amount of data
  for n in $(cat "$1"/log* | awk "{print $2}" | sort -n -S 50% | sed "$num50""$num99"'d' | tr '\n' ' '); do
    printf '%s\t' "$(round "$n")"
  done
}

printf '\tIPC\tCycles\t\tInstrs\t\tL1 hits\t\tL2 hits\t\tL3 hits\n'
printf '\t50%%\t50%%\t99%%\t50%%\t99%%\t50%%\t99%%\t50%%\t99%%\t50%%\t99%%\n'
printf '\n'
printf '\t'
d="results/TinyNF"
printf "$(med99 "$d" '$2/$1' x)"
printf "$(med99 "$d" '$1')"
printf "$(med99 "$d" '$2')"
printf "$(med99 "$d" '$3')"
printf "$(med99 "$d" '$4')"
printf "$(med99 "$d" '$5')\n"
