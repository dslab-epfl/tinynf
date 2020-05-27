#!/bin/sh

git submodule update --init --recursive

export RTE_SDK="$(dirname $(readlink -f "$0"))/dpdk"
export RTE_TARGET=x86_64-native-linuxapp-gcc

cd "$RTE_SDK"
if [ ! -d "$RTE_TARGET" ]; then
  # Remove the need for an stdin, which is really annoying to provide in scripts,
  # but keep 'c' and 'rc' used/defined so the compiler doesn't warn
  sed -i 's/rc = read(0, &c, 1);/c=0;rc=c;while(f_quit == 0) { }/' app/test-pmd/testpmd.c

  # Changes as indicated in the Test Case 4 of the DPDK 20.02 perf report
  sed -i 's/DESC_DEFAULT 1024/DESC_DEFAULT 2048/g' examples/l3fwd/l3fwd.h

  make install -j$(nproc) T=$RTE_TARGET DESTDIR=.
fi
