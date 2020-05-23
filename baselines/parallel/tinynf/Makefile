# Get this directory
THIS_DIR := $(abspath $(dir $(lastword $(MAKEFILE_LIST))))

# fancy shell stuff
SHELL := /bin/bash -O extglob -c

# Vigor dir
VIGOR_DIR := $(THIS_DIR)/../../vigor/vigor

# Vigor baseline setup script if needed
_IGNORED := $(shell $(VIGOR_DIR)/../setup.sh 2>/dev/null)

# Our main file
TN_FILES += $(THIS_DIR)/tinynf.c
# Other NAT files
TN_FILES += $(shell echo $(THIS_DIR)/../*.c)
# Vigor utility file (but not nf.c, since we have our own main!)
TN_FILES += $(VIGOR_DIR)/nf-util.c
# Vigor's libVig; boilerplate-assumptions is a stub file for builtins
TN_FILES += $(shell echo $(VIGOR_DIR)/libvig/verified/!(boilerplate-assumptions).c)

# parallel needs pthread
TN_LDFLAGS += -lpthread
# cpu_zero and friends
TN_CFLAGS += -D_GNU_SOURCE
#TN_DEBUG := 2
# Vigor expects its root dir to be an include path
TN_CFLAGS += -I $(VIGOR_DIR)

# Include the file that holds the global variables for the DPDK shim
RTE_SDK := $(THIS_DIR)/../../../shims/dpdk
RTE_TARGET := .
TN_NO_RUN_TARGET := true
DPDK_DIR := $(RTE_SDK)/$(RTE_TARGET)
TN_CFLAGS += -isystem $(DPDK_DIR)/include
TN_FILES += $(DPDK_DIR)/tn_dpdk.c

# but don't really use DPDK
TN_CFLAGS += -DTN_DPDK_PARSE_ONLY

# Vigor compiles with DPDK makefiles, which do not care about extremely many warnings, so let's not even bother
TN_CFLAGS += -w

# Use Vigor's fast power-of-2-capacity map
TN_CFLAGS += -DCAPACITY_POW2

#TN_DEBUG := 2

# Include the TinyNF makefile
include $(THIS_DIR)/../../../code/Makefile

# Include the Vigor NF's makefile, minus the other makefiles, so we can get the NF's args
VIGOR_MAKEFILE := $(shell mktemp)
_IGNORED := $(shell cat $(VIGOR_DIR)/vigpol/Makefile | grep -v 'include.*Makefile' > $(VIGOR_MAKEFILE))
include $(VIGOR_MAKEFILE)

run:
	sudo ./tinynf $(TN_ARGS) -- $(NF_ARGS)
