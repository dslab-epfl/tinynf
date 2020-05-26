#!/bin/sh

# $1: path to NF folder
summarize()
{
  lines="$(cat "$1/latencies-single/1000" | wc -l)"
  num99="$(echo "$lines - $lines * 0.99 / 1" | bc)"
  lat50="$(cat "$1/latencies-single/1000" | ministat -A | tail -n 1 | awk '{print $5}')"
  lat99="$(cat "$1/latencies-single/1000" | sort -n | tail -n $num99 | ministat -A | tail -n 1 | awk '{print $5}')"
  tput="$(cat "$1/throughput-single")"
  echo "tput $tput / lat $lat50 $lat99"
}

for nf in nat bridge lb pol fw; do
  echo "$nf"
  echo "-   DPDK: $(summarize "results/vigor-$nf-dpdk")"
  echo "- TinyNF: $(summarize "results/vigor-$nf")"
done
