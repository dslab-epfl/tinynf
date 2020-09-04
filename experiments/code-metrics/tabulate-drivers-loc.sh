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

printf '\tInit\t\tRX\t\tTX\n'
printf '\t#funs\t#LoCs\t#funs\t#LoCs\t#funs\t#LoCs\n'

for d in $DRIVERS; do
  printf '%s\t' "$d"
  for x in 'Init' 'RX' 'TX'; do
    ./count-functions-loc.py "$(get_code $d)" "data/$d-$x.md"
    printf '\t'
  done
  printf '\n'
done
