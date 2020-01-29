ifndef TN_NF
$(error Please define TN_NF to a Click NF filename without extension, e.g. 'nat')
endif

THIS_DIR := $(abspath $(dir $(lastword $(MAKEFILE_LIST))))

TN_BATCH_SIZE ?= 1

ifeq ($(RTE_TARGET),.)
compile:
	@TN_CC=g++ $(THIS_DIR)/../setup.sh >/dev/null 2>&1

run:
	@sudo $(THIS_DIR)/../click/bin/click burst=$(TN_BATCH_SIZE) --dpdk $(TN_ARGS) -- $(THIS_DIR)/$(TN_NF).click
else
# these extra cflags are a workaround for Click not compiling with DPDK 17.11
compile:
	@EXTRA_CFLAGS='-I "$(RTE_SDK)/$(RTE_TARGET)/include" --include=rte_bus_pci.h' $(THIS_DIR)/../setup.sh >/dev/null 2>&1

# the --dpdk appears necessary even if we give no args, in order to actually use DPDK
run:
	@sudo $(THIS_DIR)/../click/bin/click burst=$(TN_BATCH_SIZE) --dpdk -- $(THIS_DIR)/$(TN_NF).click

is-dpdk:
	@# yes
endif

print-nf-name:
	@echo click
