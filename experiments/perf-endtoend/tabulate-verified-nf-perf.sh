#!/bin/sh
# $1: path to NF folder

tofrac()
{
  echo "scale=2; $1 / 1000" | bc
}

summarize()
{
  tput="$(tofrac $(cat "$1/throughput-single"))"
  printf '%s\t' "$tput"

  lines="$(cat "$1/latencies-single/1000" | wc -l)"
  num50="$(echo "$lines / 2 + 1" | bc)"
  num99="$(echo "$lines * 0.99 / 1" | bc)"
  for n in $(cat "$1/latencies-single/1000" | sort -n | sed "$num50"'p;'"$num99"'q;d' | tr '\n' ' '); do
    printf '%s\t' "$(tofrac "$n")"
  done
}

printf "\tDPDK\t\t\tTinyNF\n"
printf "\tTput\tLat50\tLat99\tTput\tLat50\tLat99\n"
for nf in nat bridge lb pol fw; do
  printf "$nf\t$(summarize "results/vigor-$nf-dpdk")$(summarize "results/vigor-$nf")\n"
done
printf "\nTput is in Gb/s, lat in us\n\n"
