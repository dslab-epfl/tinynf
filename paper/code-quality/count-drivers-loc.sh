#!/bin/sh

for d in 'DPDK' 'TinyNF'; do
  path="$RTE_SDK/drivers/net/ixgbe"
  if [ "$d" != 'DPDK' ]; then
    path='../../code/net/82599'
  fi

  for x in 'initialization' 'reception' 'transmission'; do
    echo "$d $x"
    ./count-functions-loc.py "$path" "data/$d-$x.md"
  done
done
