ifndef TN_VIGOR_NF
$(error Please define TN_VIGOR_NF to a Vigor NF without the vig prefix, e.g. 'nat')
endif

# Allow the use of special patterns in shell, as Vigor does
SHELL := /bin/bash -O extglob -c

# Run the setup script, in case it hasn't been run yet
_IGNORED := $(shell ./setup.sh 2>/dev/null)

# Get the Vigor directory
VIGOR_DIR := $(abspath $(dir $(lastword $(MAKEFILE_LIST))))/vigor

# Force the auto-generation of Vigor files; pretend we have VeriFast so the auto-generation doesn't fail
_IGNORED := $(shell cd $(VIGOR_DIR)/vig$(TN_VIGOR_NF); dir=$$(mktemp -d); ln -s /bin/true "$$dir/verifast"; PATH="$$dir:$$PATH" make autogen; rm -rf "$$dir")

# Our main stub
FILES += main.c
# Vigor utility file (but not nf.c, since we have our own main!)
FILES += $(VIGOR_DIR)/nf-util.c
# Vigor NF files; don't include the loop file, Vigor only uses it during verification
FILES += $(shell echo $(VIGOR_DIR)/vig$(TN_VIGOR_NF)/!(loop).c)
# Vigor's libVig; boilerplate-assumptions is a stub file for builtins
FILES += $(shell echo $(VIGOR_DIR)/libvig/verified/!(boilerplate-assumptions).c)

# Vigor expects its root dir to be an include path
CFLAGS += -I $(VIGOR_DIR)

# Our DPDK stub headers, and the file that holds the global variables
DPDK_DIR := $(RTE_SDK)/$(RTE_TARGET)
CFLAGS += -isystem $(DPDK_DIR)/include
FILES += $(DPDK_DIR)/tn_dpdk.c

# Vigor compiles with DPDK makefiles, which do not care about all those...
CFLAGS += -Wno-reserved-id-macro -Wno-sign-conversion -Wno-missing-prototypes -Wno-unused-parameter -Wno-unused-value -Wno-unused-function \
          -Wno-padded -Wno-tautological-unsigned-zero-compare -Wno-missing-variable-declarations -Wno-implicit-int-conversion -Wno-shorten-64-to-32 \
          -Wno-extra-semi-stmt -Wno-gnu-zero-variadic-macro-arguments -Wno-empty-translation-unit -Wno-newline-eof -Wno-unused-variable -Wno-c++-compat \
          -Wno-gnu-empty-struct -Wno-strict-prototypes -Wno-sign-compare -Wno-missing-noreturn

# Use Vigor's fast power-of-2-capacity map
CFLAGS += -DCAPACITY_POW2

# LTO makes a huge difference in Vigor perf (e.g. VigNAT goes from 4G to 8G)
CFLAGS += -flto
LDFLAGS += -flto

# Include the TinyNF makefile
include ../../code/Makefile

# Include the Vigor NF's makefile, minus the other makefiles, so we can get the NF's args
VIGOR_MAKEFILE := $(shell mktemp)
_IGNORED := $(shell cat $(VIGOR_DIR)/vig$(TN_VIGOR_NF)/Makefile | grep -v 'include.*Makefile' > $(VIGOR_MAKEFILE))
include $(VIGOR_MAKEFILE)

run:
	sudo ./tinynf $(TN_ARGS) -- $(NF_ARGS)
