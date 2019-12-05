ifndef TN_NF
$(error Please define TN_NF to a Vigor NF without the vig prefix, e.g. 'nat')
endif

# Allow the use of special patterns in shell, as Vigor does
SHELL := /bin/bash -O extglob -c

# Get this directory
THIS_DIR := $(abspath $(dir $(lastword $(MAKEFILE_LIST))))

# Run the setup script, in case it hasn't been run yet
_IGNORED := $(shell $(THIS_DIR)/setup.sh 2>/dev/null)

# Get the Vigor directory
VIGOR_DIR := $(abspath $(dir $(lastword $(MAKEFILE_LIST))))/vigor

# Force the auto-generation of Vigor files; pretend we have VeriFast so the auto-generation doesn't fail
_IGNORED := $(shell cd $(VIGOR_DIR)/vig$(TN_NF); dir=$$(mktemp -d); ln -s /bin/true "$$dir/verifast"; PATH="$$dir:$$PATH" make autogen; rm -rf "$$dir")

# Our main stub
TN_FILES += main.c
# Vigor utility file (but not nf.c, since we have our own main!)
TN_FILES += $(VIGOR_DIR)/nf-util.c
# Vigor NF files; don't include the loop file, Vigor only uses it during verification
TN_FILES += $(shell echo $(VIGOR_DIR)/vig$(TN_NF)/!(loop).c)
# Vigor's libVig; boilerplate-assumptions is a stub file for builtins
TN_FILES += $(shell echo $(VIGOR_DIR)/libvig/verified/!(boilerplate-assumptions).c)

# Vigor expects its root dir to be an include path
TN_CFLAGS += -I $(VIGOR_DIR)

# Our DPDK stub headers, and the file that holds the global variables
RTE_SDK := $(THIS_DIR)/../../shims/dpdk
RTE_TARGET := .
DPDK_DIR := $(RTE_SDK)/$(RTE_TARGET)
TN_CFLAGS += -isystem $(DPDK_DIR)/include
TN_FILES += $(DPDK_DIR)/tn_dpdk.c

# Vigor compiles with DPDK makefiles, which do not care about extremely many warnings, so let's not even bother
TN_CFLAGS += -w

# Use Vigor's fast power-of-2-capacity map
TN_CFLAGS += -DCAPACITY_POW2

# Include the TinyNF makefile
include ../../code/Makefile

# Include the Vigor NF's makefile, minus the other makefiles, so we can get the NF's args
VIGOR_MAKEFILE := $(shell mktemp)
_IGNORED := $(shell cat $(VIGOR_DIR)/vig$(TN_NF)/Makefile | grep -v 'include.*Makefile' > $(VIGOR_MAKEFILE))
include $(VIGOR_MAKEFILE)

run:
	@sudo ./tinynf $(TN_ARGS) -- $(NF_ARGS)
