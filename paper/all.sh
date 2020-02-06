#!/bin/sh

# Vigor full info
for nf in nop nat fw bridge pol; do
  ./bench-nf.py ../baselines/vigor $nf
done

# Vigor comparison, using the same config as Vigor if possible
if [ -f '../benchmarking/config-vigor' ]; then cp ../benchmarking/config-vigor ../benchmarking/config -b; fi
for nf in nop nat fw bridge pol; do
  ./bench-nf.py ../baselines/vigor $nf single
done
if [ -f '../benchmarking/config-vigor' ]; then mv ../benchmarking/config~ ../benchmarking/config; fi

# Click NOP full info
./bench-nf.py ../baselines/click nop
