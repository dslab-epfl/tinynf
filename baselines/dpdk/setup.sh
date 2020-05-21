#!/bin/sh

git submodule update --init --recursive

export RTE_SDK="$(pwd)/dpdk"
export RTE_TARGET=x86_64-native-linuxapp-gcc

cd dpdk
if [ ! -d "$RTE_TARGET" ]; then
  # Remove the need for an stdin, which is really annoying to provide in scripts,
  # but keep 'c' and 'rc' used/defined so the compiler doesn't warn
  sed -i 's/rc = read(0, &c, 1);/c=0;rc=c;while(f_quit == 0) { }/' app/test-pmd/testpmd.c

  make install -j$(nproc) T=$RTE_TARGET DESTDIR=.
fi
