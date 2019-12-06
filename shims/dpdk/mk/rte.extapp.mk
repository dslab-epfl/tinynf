# This is the second Makefile that DPDK applications include.
# Note that Click does not include this, it makes its own private copy of it.
#
# Its main purpose is to define an 'all' target that compiles users' files in $(SRCS-y) into build/app/$(APP).
# Users also expect that their $(CFLAGS) and $(LDFLAGS) settings will be respected.
# However, because we're using TinyNF underneath, we can afford to do better;
# so we use the TinyNF compiler and flags, to allow for e.g. LTO.

BUILDDIR := ./build

all:
	@rm -rf "$(BUILDDIR)"
	@mkdir -p "$(BUILDDIR)/app"
	@for file in $(SRCS-y); do $(TN_CC) -c "$$file" $(CFLAGS) $(TN_CFLAGS) -I "$(TN_DPDK_DIR)/include" -o "$(BUILDDIR)/$$(basename $$file).o"; done
	@$(TN_CC) "$(BUILDDIR)/"*.o "$(TN_DPDK_DIR)/lib/libdpdk.so" $(LDFLAGS) $(TN_LDFLAGS) -o "$(BUILDDIR)/app/$(APP)"
