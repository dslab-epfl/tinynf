# Standard DPDK makefile included by projects that use DPDK such as Vigor
# Projects expect an 'all' target that compiles the $(SRCS-y) files using $(CC) $(CFLAGS) and $(LD) $(LDFLAGS) into $(PWD)/build/app/$(APP), linking with DPDK

all:
	rm -rf "$(PWD)/build"
	mkdir -p "$(PWD)/build/app"
	for file in $(SRCS-y); do $(CC) -c "$$file" $(CFLAGS) -I "$(TN_DPDK_DIR)/include" -o "$(PWD)/build/$$(basename $$file).o"; done
	$(LD) "$(PWD)/build/"*.o "$(TN_DPDK_DIR)/lib/libdpdk.so" $(LDFLAGS) $(TN_LDFLAGS) -o "$(PWD)/build/app/$(APP)"
