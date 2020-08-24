#!/bin/sh
# $1: path to NF folder

tofrac()
{
  echo "scale=2; $1 / 1000" | bc
}

summarize()
{
  lines="$(cat "$1/latencies-single/1000" | wc -l)"
  num99="$(echo "$lines - $lines * 0.99 / 1" | bc)"
  lat50="$(tofrac $(cat "$1/latencies-single/1000" | ministat -A | tail -n 1 | awk '{print $5}'))"
  lat99="$(tofrac $(cat "$1/latencies-single/1000" | sort -n | tail -n $num99 | ministat -A | tail -n 1 | awk '{print $5}'))"
  tput="$(tofrac $(cat "$1/throughput-single"))"

  printf "$tput\t$lat50\t$lat99"
}

printf "\tDPDK\t\t\tTinyNF\n"
printf "\tTput\tLat50\tLat99\tTput\tLat50\tLat99\n"
for nf in nat bridge lb pol fw; do
  printf "$nf\t$(summarize "results/vigor-$nf-dpdk")\t$(summarize "results/vigor-$nf")\n"
done
printf "\nTput is in Gb/s, lat in us\n\n"
