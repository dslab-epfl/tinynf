ifndef TN_NF
$(error Please define TN_NF to a Vigor NF without the vig prefix, e.g. 'nat')
endif

THIS_DIR := $(abspath $(dir $(lastword $(MAKEFILE_LIST))))
VIGOR_DIR := $(THIS_DIR)/../vigor

# Run the setup script, in case it hasn't been run yet
_IGNORED := $(shell $(THIS_DIR)/../setup.sh 2>/dev/null)

# Vigor's make run always compiles, so no need to have a separate compile step
ifeq ($(RTE_TARGET),.)
compile:
	@# nothing

run:
	@NF_DPDK_ARGS="$(TN_ARGS)" make -C $(VIGOR_DIR)/vig$(TN_NF) run
else
compile:
	@$(THIS_DIR)/../../reset-dpdk.sh $(TN_ARGS)

run:
	@make -C $(VIGOR_DIR)/vig$(TN_NF) run
endif

print-nf-name:
	@echo nf
