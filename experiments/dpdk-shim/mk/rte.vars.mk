# This is the first Makefile that DPDK applications include.
# It defines variables DPDK apps expect in their Makefile.

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
