# This is the second Makefile that DPDK applications include.
# Note that Click does not include this, it makes its own private copy of it.
#
# Its main purpose is to define an 'all' target that compiles users' files in $(SRCS-y) into build/app/$(APP).
# Users also expect that their $(CFLAGS) and $(LDFLAGS) settings will be respected.
# However, because we're using TinyNF underneath, we can afford to do better;
# so we use the TinyNF compiler and flags, to allow for e.g. LTO.

TN_DPDK_DIR := $(abspath $(dir $(lastword $(MAKEFILE_LIST))))/..
TN_DIR := $(TN_DPDK_DIR)/../../code
TN_FILES := $(TN_DPDK_DIR)/tn_dpdk.c
TN_NO_DEFAULT_TARGET := true
include $(TN_DIR)/Makefile

BUILDDIR := ./build

all:
	@rm -rf "$(BUILDDIR)"
	@mkdir -p "$(BUILDDIR)/app"
	@for file in $(SRCS-y) $(TN_FILES); do $(TN_CC) $(CFLAGS) $(TN_CFLAGS) -I "$(TN_DPDK_DIR)/include" -c "$$file" -o "$(BUILDDIR)/$$(basename $$file).o"; done
	@$(TN_CC) $(LDFLAGS) $(TN_CFLAGS) "$(BUILDDIR)/"*.o -o "$(BUILDDIR)/app/$(APP)"
