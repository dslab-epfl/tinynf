#!/bin/sh

for nf in nat fw bridge pol; do # nop
  ./bench-nf.py ../baselines/vigor $nf
done

./bench-nf.py ../baselines/click nop
