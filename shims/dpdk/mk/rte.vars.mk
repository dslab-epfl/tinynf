# This is the first Makefile that DPDK applications include.
#
# It has two goals:
# - Generate the DPDK shim library
# - Define variables that DPDK apps expect in their Makefile, including linking to the shim library
# - Define variables that Click expects for its Makefile, i.e. internal DPDK variables

# First step: generate the "DPDK" library, a.k.a. our stub with global variables
# This is not a target, we always do it, since DPDK apps expect DPDK to already be compiled.
# We use the TinyNF variables to do this, since users do not expect their variables to affect DPDK
TN_DPDK_DIR := $(abspath $(dir $(lastword $(MAKEFILE_LIST))))/..
TN_DPDK_LIB_SO := $(TN_DPDK_DIR)/lib/libdpdk.so
TN_DIR := $(TN_DPDK_DIR)/../../code
TN_FILES := $(TN_DPDK_DIR)/tn_dpdk.c
TN_NO_DEFAULT_TARGET := true # don't expose our own target
include $(TN_DIR)/Makefile
_IGNORED := $(shell mkdir -p "$(TN_DPDK_DIR)/lib"; \
                    $(TN_CC) -shared -fPIC $(TN_CFLAGS) -I $(TN_DPDK_DIR)/include $(TN_FILES) -o "$(TN_DPDK_LIB_SO)")

# Click depends on this variable existing
RTE_SDK_BIN := $(RTE_SDK)/$(RTE_TARGET)

# Statically link our libdpdk so we don't have to mess with LD_LIBRARY_PATH
EXTRA_LDLIBS += "$(TN_DPDK_LIB_SO)" $(TN_LDFLAGS)

# Define constants such that Click won't try to include any object files whatsoever
# These should be 'y' or 'n'; but for COMBINE_LIBS, we set it to 'x' so that it's completely ignored
# and thus Click will neither include libs individually nor include the overall lib
CONFIG_RTE_BUILD_COMBINE_LIBS=x
CONFIG_RTE_LIBRTE_PMD_PCAP=n
CONFIG_RTE_LIBRTE_PMD_SZEDATA2=n
CONFIG_RTE_LIBRTE_VHOST_NUMA=n
CONFIG_RTE_LIBRTE_VHOST_USER=y
