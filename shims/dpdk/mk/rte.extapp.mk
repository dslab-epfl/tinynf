# Standard DPDK makefile included by projects that use DPDK such as Vigor

all:
	rm -rf $(PWD)/build
	mkdir -p $(PWD)/build/app
	for file in $(SRCS-y); do gcc -c "$$file" $(CFLAGS) -I "$(TN_DPDK_DIR)/include" -o "$(PWD)/build/$$(basename $$file).o"; done
	gcc $(PWD)/build/*.o $(TN_DPDK_DIR)/lib/libdpdk.so -lnuma -o $(PWD)/build/app/nf
