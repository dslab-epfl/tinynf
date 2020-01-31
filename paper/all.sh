#!/bin/sh

# Vigor NOP / NAT full info
for nf in nop nat; do
  ./bench-nf.py ../baselines/vigor $nf
done

# Click NOP full info
./bench-nf.py ../baselines/click nop

# Vigor comparison
for nf in nop nat fw bridge pol; do
  ./bench-nf.py ../baselines/vigor $nf simple
done

