#!/bin/bash

CPU_ASSIGNED=2
NETWORK_DEVICE_ADDRESS_1=02:00.0
NETWORK_DEVICE_ADDRESS_2=02:00.0

function usage() {
  echo "Usage:"
  echo "   $0"
  echo "or"
  echo "   $0 -d  #To run with gdb"
}

function clean_and_build() {
  make clean
  make
  echo ""
  echo "-----------------------------"
  echo "Start execution :"
  echo "-----------------------------"
  echo ""
}

if [ $# -eq 0 ]
then
  clean_and_build
  sudo taskset -c $CPU_ASSIGNED ./tinynf $NETWORK_DEVICE_ADDRESS_1 $NETWORK_DEVICE_ADDRESS_2
elif [ $# -eq 1 ] && [ "$1" = "-d" ]
then
  clean_and_build
  # Run with gdb
  sudo taskset -c $CPU_ASSIGNED gdb -ex run --args ./tinynf $NETWORK_DEVICE_ADDRESS_1 $NETWORK_DEVICE_ADDRESS_2
else
  usage
fi
