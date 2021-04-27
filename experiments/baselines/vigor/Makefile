ifndef TN_NF
$(error Please define TN_NF to a Vigor NF without the vig prefix, e.g. 'nat')
endif

# Get this directory
THIS_DIR := $(abspath $(dir $(lastword $(MAKEFILE_LIST))))

# Get the Vigor directory
VIGOR_DIR := $(abspath $(dir $(lastword $(MAKEFILE_LIST))))/vigor

# Use our own DPDK shim, and do that also for sub-commands
RTE_SDK := $(THIS_DIR)/../../dpdk-shim
RTE_TARGET := .
SHELL := RTE_SDK='$(RTE_SDK)' RTE_TARGET='$(RTE_TARGET)' /bin/bash -O extglob -c

# Run the setup script, in case it hasn't been run yet
_IGNORED := $(shell cd $(THIS_DIR); ./setup.sh 2>/dev/null)

# Our main stub
TN_FILES += $(THIS_DIR)/main.c
# Vigor utility file (but not nf.c, since we have our own main!)
TN_FILES += $(VIGOR_DIR)/nf-util.c
# Vigor NF files; don't include the loop file, Vigor only uses it during verification
TN_FILES += $(shell echo $(VIGOR_DIR)/vig$(TN_NF)/!(loop).c)
# Vigor's libVig
TN_FILES += $(shell echo $(VIGOR_DIR)/libvig/verified/*.c)

# Vigor expects its root dir to be an include path
TN_CFLAGS += -I $(VIGOR_DIR)

# Include the file that holds the global variables for the DPDK shim
DPDK_DIR := $(RTE_SDK)/$(RTE_TARGET)
TN_CFLAGS += -isystem $(DPDK_DIR)/include
TN_FILES += $(DPDK_DIR)/tn_dpdk.c

# Vigor compiles with DPDK makefiles, which do not care about extremely many warnings, so let's not even bother
TN_CFLAGS += -w

# Use Vigor's fast power-of-2-capacity map
TN_CFLAGS += -DCAPACITY_POW2

# Put it here regardless of who's invoking us
TN_APP := $(THIS_DIR)/tinynf

# Include the TinyNF makefile
include $(THIS_DIR)/../../../code/Makefile
