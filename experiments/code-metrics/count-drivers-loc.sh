#!/bin/sh

for d in 'TinyNF' 'Ixy' 'DPDK'; do
  path='../../code/net/82599'
  if [ "$d" = 'Ixy' ]; then
    path="../../baselines/ixy/ixy/src/driver"
  fi
  if [ "$d" = 'DPDK' ]; then
    path="$RTE_SDK/drivers/net/ixgbe"
  fi

  for x in 'initialization' 'reception' 'transmission'; do
    echo "$d $x"
    ./count-functions-loc.py "$path" "data/$d-$x.md"
  done
done
