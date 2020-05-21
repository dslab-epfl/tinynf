#!/bin/sh

#git submodule update --init --recursive

export RTE_SDK="$(pwd)/dpdk"
export RTE_TARGET=x86_64-native-linuxapp-gcc

cd dpdk
make install -j$(nproc) T=x86_64-native-linuxapp-gcc DESTDIR=.
