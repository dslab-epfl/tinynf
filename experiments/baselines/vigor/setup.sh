#!/bin/sh

git submodule update --init --recursive

# Simplified version of the vigor setup script, we use the pregenerated branch so nothing else is needed
# We have two DPDKs: one "verified" with the Vigor patches (which e.g. disable vectorization), one "unverified" for batching

sudo apt-get install -y libnuma-dev

RTE_TARGET='x86_64-native-linuxapp-gcc'

cd dpdk
if [ ! -d $RTE_TARGET ]; then
  # Ignore warnings caused by GCC 10
  EXTRA_CFLAGS='-Wno-stringop-truncation -Wno-stringop-overflow -Wno-zero-length-bounds' make install -j$(nproc) T=$RTE_TARGET DESTDIR=.
fi
cd ..

cd dpdk-verified
if [ ! -d $RTE_TARGET ]; then
  for p in ../vigor/setup/dpdk.*.patch; do
    patch -p1 < "$p"
  done

  # same but with one more due to the patches
  EXTRA_CFLAGS='-Wno-stringop-truncation -Wno-stringop-overflow -Wno-zero-length-bounds -Wno-unused-variable' make install -j$(nproc) T=$RTE_TARGET DESTDIR=.
fi
