git submodule update --init --recursive

export RTE_SDK="$(pwd)/../../shims/dpdk"
export RTE_TARGET=.
export TN_CC=g++

cd click

if [ ! -f 'Makefile' ]; then
  cp ../tinynf.* elements/userlevel/.

  ./configure --enable-dpdk --enable-user-multithread
fi

FLAGS="$TN_CFLAGS $TN_CC $RTE_SDK $RTE_TARGET"
if [ ! -f '.flags' ] || [ "$(cat .flags)" != "$FLAGS" ]; then
  make clean
  EXTRA_CFLAGS="$TN_CFLAGS" make
  echo "$FLAGS" > '.cflags'
fi
