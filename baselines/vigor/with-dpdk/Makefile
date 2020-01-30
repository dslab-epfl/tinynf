ifndef TN_NF
$(error Please define TN_NF to a Vigor NF without the vig prefix, e.g. 'nat')
endif

THIS_DIR := $(abspath $(dir $(lastword $(MAKEFILE_LIST))))
VIGOR_DIR := $(THIS_DIR)/../vigor

# Run the setup script, in case it hasn't been run yet
_IGNORED := $(shell $(THIS_DIR)/../setup.sh 2>/dev/null)

TN_BATCH_SIZE ?= 1

# Vigor's make run always compiles, so no need to have a separate compile step
compile:
	@# nothing

ifeq ($(RTE_TARGET),.)
run:
	@NF_DPDK_ARGS="$(TN_ARGS)" make -C $(VIGOR_DIR)/vig$(TN_NF) run
else
run:
	@EXTRA_CFLAGS="-DVIGOR_BATCH_SIZE=$(TN_BATCH_SIZE) -DVIGOR_ALLOW_DROPS" make -C $(VIGOR_DIR)/vig$(TN_NF) run

is-dpdk:
	@# yes
endif

print-nf-name:
	@echo nf
