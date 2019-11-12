export RTE_SDK="$(pwd)/../../shims/dpdk"
export RTE_TARGET=.

cd click
if [ ! -f 'Makefile' ]; then
  ./configure --enable-dpdk --enable-user-multithread
fi
if [ ! -f 'bin/click' ]; then
  make
fi
