#!/bin/sh

git submodule update --init --recursive

printf 'This is going to take a few minutes...\n\n'

DRIVERS='DPDK Ixy TinyNF'

get_code()
{
  if [ "$1" = 'Ixy' ]; then
    printf '../baselines/ixy/ixy/src/driver'
  elif [ "$1" = 'DPDK' ]; then
    printf '../baselines/dpdk/dpdk/drivers/net/ixgbe'
  else
    printf '../../code/net/82599'
  fi
}

printf '\t\t%s\t%s\t%s\n' $DRIVERS

for x in 'Init' 'RX' 'TX'; do
  printf '%s\tFuncs\t' $x
  for d in $DRIVERS; do
    printf '%s\t' $(./count-functions-loc.py "$(get_code $d)" "data/$d-$x.md" function-count)
  done
  printf '\n'
  printf '\tLoC\t'
  for d in $DRIVERS; do
    printf '%s\t' $(./count-functions-loc.py "$(get_code $d)" "data/$d-$x.md")
  done
  printf '\n'
done
