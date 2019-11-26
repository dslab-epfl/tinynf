#!/bin/bash

for nf in nop nat fw bridge pol; do
  ./bench-matrix.sh ../baselines/vigor/with-dpdk dpdk $nf
  ./bench-matrix.sh ../baselines/vigor/with-dpdk dpdk-shim $nf
  ./bench-matrix.sh ../baselines/vigor custom $nf
done

./bench-matrix.sh ../baselines/click/with-dpdk dpdk nop
./bench-matrix.sh ../baselines/click/with-dpdk dpdk-shim nop
./bench-matrix.sh ../baselines/click custom nop
