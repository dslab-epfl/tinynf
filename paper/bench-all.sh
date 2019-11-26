#!/bin/sh

for nf in nop nat fw bridge pol; do
  ./bench-nf.py ../baselines/vigor $nf
done

./bench-nf.py ../baselines/click nop
