export RTE_SDK="$(pwd)/../../shims/dpdk"
export RTE_TARGET=.
export TN_CC=g++

cd click

if [ ! -f 'Makefile' ]; then
  ./configure --enable-dpdk --enable-user-multithread
fi

if [ ! -f '.cflags' ] || [ "$(cat .cflags)" != "$TN_CFLAGS" ]; then
  make clean
  make
  echo "$TN_CFLAGS" > '.cflags'
fi
