#!/bin/sh

printf 'Tabulating results... This will take around an hour due to the amount of data involved.\n\n'

round()
{
  # use sed to print 0.00 if the number is 0, and the leading zero if the number is >0 and <1
  echo "scale=2; $1 / 1" | bc | sed 's/^0$/0.00/' | sed 's/^\./0./'
}


med99()
{
  lines="$(cat "$1"/log* | wc -l)"
  num50="$(echo "$lines / 2" | bc)p;"
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

for driver in 'DPDK-1' 'DPDK-32' 'TinyNF'; do
  printf '%s\n' "$driver"
  for nf in 'nop' 'write' 'lookup' 'pol'; do
    if [ -d "results/$nf" ]; then
      printf ' %s\t' "$nf"
      d="results/$nf/$driver"
      printf "$(med99 "$d" '$2/$1' x)"
      printf "$(med99 "$d" '$1')"
      printf "$(med99 "$d" '$2')"
      printf "$(med99 "$d" '$3')"
      printf "$(med99 "$d" '$4')"
      printf "$(med99 "$d" '$5')\n"
    fi
  done
done
