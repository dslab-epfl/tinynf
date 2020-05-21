 # Get this directory
THIS_DIR := $(abspath $(dir $(lastword $(MAKEFILE_LIST))))

# Run the setup script, in case it hasn't been run yet
_IGNORED := $(shell $(THIS_DIR)/setup.sh 2>/dev/null)

TN_BATCH_SIZE ?= 1

# Burst sizes less than 4 need non-power-of-2 ring sizes, but they still need to be multiples of 32, so we add 32 to the defaults
ifeq (1,$(shell echo '$(TN_BATCH_SIZE) < 4' | bc))
ADDITIONAL_PARAMS=--rxd=160 --txd=544
endif

compile:
	@# nothing

run:
	@sudo $(RTE_SDK)/$(RTE_TARGET)/build/app/test-pmd/testpmd -n 2 -- \
	      --auto-start --port-topology=chained --forward-mode=mac \
	      --eth-peer=0,00:00:00:00:00:00 --eth-peer=1,00:00:00:00:00:01 \
	      --burst=$(TN_BATCH_SIZE) $(ADDITIONAL_PARAMS)
