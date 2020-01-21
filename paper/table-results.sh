#!/bin/sh

find_tput_lat()
{
  kind="$1"
  nf="$2"
  type="$3"

  best_tput=0
  lat=0
  for param in $(ls -1 "results/$kind/$nf/$type" | sort -n); do
    param_folder="results/$kind/$nf/$type/$param"
    tput=$(cat "$param_folder/throughput")
    if [ "$tput" -gt "$best_tput" ]; then
      best_tput="$tput"
      high_lat=$(ls -1 "$param_folder/latencies" | sort -n | tail -n 1)
      lat=$(cat "$param_folder/latencies/$high_lat" | ministat -A | tail -n 1 | awk '{printf "%.0f\t%.0f", $5, $7}')
    fi
  done
  printf "%s\t%s" "$best_tput" "$lat"
}


echo "NF\t\tTinyNF\t\t\tDPDK"
echo "  \t\tTput\tLatMed\tLatDev\tTput\tLatMed\tLatDev"
for kind in $(ls -1 "results" | sort); do
  for nf in $(ls -1 "results/$kind" | sort); do
    tn_type='custom, simple'
    if [ "$nf" = 'bridge' ]; then tn_type='custom'; fi
    tn_best=$(find_tput_lat "$kind" "$nf" "$tn_type")

    dpdk_best=$(find_tput_lat "$kind" "$nf" "original")
    echo "$kind $nf\t$tn_best\t$dpdk_best"
  done
done
