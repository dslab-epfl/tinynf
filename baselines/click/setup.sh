export RTE_SDK="$(pwd)/../../shims/dpdk"
export RTE_TARGET=.

cd click
./configure --enable-dpdk --enable-user-multithread
make
