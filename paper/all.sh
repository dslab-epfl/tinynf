#!/bin/sh

# Click NOP full info
./bench-nf.py ../baselines/click nop

# Vigor full info + comparison
for nf in nop nat fw bridge pol; do
  ./bench-nf.py ../baselines/vigor $nf
  ./bench-nf.py ../baselines/vigor $nf single
done

