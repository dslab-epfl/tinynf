ifndef TN_NF
$(error Please define TN_NF to a Click NF filename without extension, e.g. 'nat')
endif

THIS_DIR := $(abspath $(dir $(lastword $(MAKEFILE_LIST))))

compile:
	@RTE_SDK=$(THIS_DIR)/../../shims/dpdk RTE_TARGET=. TN_CC=g++ $(THIS_DIR)/setup.sh >/dev/null 2>&1

run:
	@sudo $(THIS_DIR)/click/bin/click dev0=$(word 1,$(TN_ARGS)) dev1=$(word 2,$(TN_ARGS)) $(THIS_DIR)/$(TN_NF).click

print-nf-name:
	@echo click
