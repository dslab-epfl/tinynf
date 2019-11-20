ifndef TN_NF
$(error Please define TN_NF to a Vigor NF without the vig prefix, e.g. 'nat')
endif

# Get the Vigor directory
#VIGOR_DIR := $(abspath $(dir $(lastword $(MAKEFILE_LIST))))/../vigor

# Include the Vigor NF's makefile, minus the other makefiles, so we can get the NF's args
#VIGOR_MAKEFILE := $(shell mktemp)
#_IGNORED := $(shell cat $(VIGOR_DIR)/vig$(TN_NF)/Makefile | grep -v 'include.*Makefile' > $(VIGOR_MAKEFILE))
#include $(VIGOR_MAKEFILE)

compile:
	# Nothing!

run:
	NF_DPDK_ARGS="$(TN_ARGS)" LD=gcc TN_CC=gcc make -C ../vigor/vig$(TN_NF) run
