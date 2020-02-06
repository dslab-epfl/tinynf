#!/bin/sh

# $1: path to NF folder
summarize()
{
  lat="$(cat "$1/latencies-single/1000" | ministat -A | tail -n 1 | awk '{print $5}')"
  tput="$(cat "$1/throughput-single")"
  echo "lat $lat, tput $tput"
}

for nf in nop nat bridge pol fw; do
  custkey='custom, simple'
  if [ "$nf" = 'bridge' ]; then custkey='custom'; fi
  echo "$nf"
  echo "- Vigor (Linux): $(summarize "results/vigor/$nf/original/1")"
  echo "-        TinyNF: $(summarize "results/vigor/$nf/$custkey/1")"
  echo "- Vigor with unverified batching: $(summarize "results/vigor/$nf/original/64")"
done
