#!/bin/sh

git submodule update --init --recursive

export RTE_SDK="$(pwd)/dpdk"
export RTE_TARGET=x86_64-native-linuxapp-gcc

cd dpdk
if [ ! -d "$RTE_TARGET" ]; then
  make install -j$(nproc) T=$RTE_TARGET DESTDIR=.
fi
