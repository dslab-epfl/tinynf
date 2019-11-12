ifndef TN_CLICK_NF
$(error Please define TN_CLICK_NF to a Click NF filename without extension, e.g. 'nat')
endif

THIS_DIR := $(abspath $(dir $(lastword $(MAKEFILE_LIST))))

# Run the setup script, in case it hasn't been run yet
_IGNORED := $(shell $(THIS_DIR)/setup.sh 2>/dev/null)

default:
	# Nothing!

run:
#	@printf '\n\n!!!\nClick may incorrectly claim that the CPU\n'
#	@printf 'cores are not on the same NUMA node as the NICs, ignore this.\n!!!\n\n'
	@sudo $(THIS_DIR)/click/bin/click burst=1 --dpdk $(TN_ARGS) -- $(THIS_DIR)/$(TN_CLICK_NF).click
