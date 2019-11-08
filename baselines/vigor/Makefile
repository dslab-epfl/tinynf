ifndef TN_VIGOR_NF
$(error Please define TN_VIGOR_NF to a Vigor NF, e.g. 'vignat')
endif

# Allow the use of special patterns in shell, as Vigor does
SHELL := /bin/bash -O extglob -c

# Run the setup script, in case it hasn't been run yet
_IGNORED := $(shell ./setup.sh 2>/dev/null)

# Get the Vigor directory
VIGOR_DIR := $(abspath $(dir $(lastword $(MAKEFILE_LIST))))/vigor

# Force the auto-generation of Vigor files; pretend we have VeriFast so the auto-generation doesn't fail
_IGNORED := $(shell cd $(VIGOR_DIR)/$(TN_VIGOR_NF); dir=$$(mktemp -d); ln -s /bin/true "$$dir/verifast"; PATH="$$dir:$$PATH" make autogen; rm -rf "$$dir")

ifeq (true,$(TN_VIGOR_CUSTOM))
# Our main stub
FILES += main.c
# Vigor files except the main one
FILES += $(VIGOR_DIR)/nf-util.c
else
# All Vigor files
FILES += $(shell echo $(VIGOR_DIR)/nf*.c)
endif

# Vigor NF files; don't include the loop file, Vigor only uses it during verification
FILES += $(shell echo $(VIGOR_DIR)/$(TN_VIGOR_NF)/!(loop).c)
# Vigor's libVig; boilerplate-assumptions is a stub file for builtins
FILES += $(shell echo $(VIGOR_DIR)/libvig/verified/!(boilerplate-assumptions).c)

# Vigor expects its root dir to be an include path
CFLAGS += -I $(VIGOR_DIR)

# Our DPDK stub headers, and the file that holds the global variables
CFLAGS += -isystem dpdk
FILES += dpdk/tn_dpdk.c

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

# Finally, include the TinyNF makefile
include ../../code/Makefile
