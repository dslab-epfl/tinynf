# Click depends on this variable existing
RTE_SDK_BIN := $(RTE_SDK)/$(RTE_TARGET)

# Define constants such that Click won't try to include any object files whatsoever
# These should be 'y' or 'n'; but for COMBINE_LIBS, we set it to 'x' so that it's completely ignored
# and thus Click will neither include libs individually nor include the overall lib
CONFIG_RTE_BUILD_COMBINE_LIBS=x
CONFIG_RTE_LIBRTE_PMD_PCAP=n
CONFIG_RTE_LIBRTE_PMD_SZEDATA2=n
CONFIG_RTE_LIBRTE_VHOST_NUMA=n
CONFIG_RTE_LIBRTE_VHOST_USER=y

# Generate the "DPDK" library, a.k.a. our stub with global variables
TN_DPDK_DIR := $(abspath $(dir $(lastword $(MAKEFILE_LIST))))/..
TN_DIR := $(TN_DPDK_DIR)/../../code
TN_FILES := $(TN_DPDK_DIR)/tn_dpdk.c
include $(TN_DIR)/Makefile
_IGNORED := $(shell mkdir -p "$(TN_DPDK_DIR)/lib"; \
                    $(TN_CC) -shared -fPIC $(TN_CFLAGS) -I$(TN_DPDK_DIR)/include $(TN_FILES) -o "$(TN_DPDK_DIR)/lib/libdpdk.so")

# Statically link our libdpdk so we don't have to mess with LD_LIBRARY_PATH (and don't forget libnuma!)
EXTRA_LDLIBS += "$(TN_DPDK_DIR)/lib/libdpdk.so" $(TN_LDFLAGS)
