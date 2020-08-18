#!/bin/sh

git submodule update --init --recursive

# Simplified version of the vigor setup script, we use the pregenerated branch so nothing else is needed

sudo apt-get install -y libnuma-dev

cd dpdk

for p in ../vigor/setup/dpdk.*.patch; do
  patch -p1 < "$p"
done

make install -j$(nproc) T=x86_64-native-linuxapp-gcc DESTDIR=.
