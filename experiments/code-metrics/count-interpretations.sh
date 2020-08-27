#!/bin/sh

grep INTERPRETATION- ../../code/net/82599/ixgbe.c | awk '{print $2}' | cut -d ':' -f 1 | cut -d '-' -f 2 | sort | uniq -c
