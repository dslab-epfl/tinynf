#!/bin/sh
set -x

git submodule update --init --recursive

cd "$(dirname "$(readlink -f "$0")")/click"

FLAGS="$TN_CFLAGS $TN_LDFLAGS $TN_CC $EXTRA_CFLAGS $RTE_SDK $RTE_TARGET"
if [ ! -f '.flags' ] || [ "$(cat .flags)" != "$FLAGS" ]; then
  # Don't always copy them because Click EXPORT_ELEMENT macros are grepped so they ignore ifdefs
  rm -f elements/userlevel/tinynf.*
  if [ "$RTE_TARGET" = '.' ]; then cp ../tinynf.* elements/userlevel/.; fi

  ./configure --enable-dpdk --enable-user-multithread
  make clean
  EXTRA_CFLAGS="$TN_CFLAGS $EXTRA_CFLAGS" make
  echo "$FLAGS" > '.flags'
fi
