#!/bin/bash

make clean
make
echo ""
echo "-----------------------------"
echo "Start execution :"
echo "-----------------------------"
echo ""

sudo taskset -c 2 ./tinynf 02:00.0 02:00.0
