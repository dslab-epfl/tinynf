# Standard DPDK makefile included by projects that use DPDK such as Vigor
# Projects expect an 'all' target that compiles the $(SRCS-y) files using $(CFLAGS) / $(LDFLAGS) into ./build/app/$(APP), linking with DPDK

BUILDDIR := ./build

all:
	@rm -rf "$(BUILDDIR)"
	@mkdir -p "$(BUILDDIR)/app"
	@for file in $(SRCS-y); do $(CC) -c "$$file" $(CFLAGS) $(TN_CFLAGS) -I "$(TN_DPDK_DIR)/include" -o "$(BUILDDIR)/$$(basename $$file).o"; done
	@$(CC) "$(BUILDDIR)/"*.o "$(TN_DPDK_DIR)/lib/libdpdk.so" $(LDFLAGS) $(TN_LDFLAGS) -o "$(BUILDDIR)/app/$(APP)"
