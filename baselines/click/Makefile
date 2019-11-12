ifndef TN_NF
$(error Please define TN_NF to a Click NF filename without extension, e.g. 'nat')
endif

THIS_DIR := $(abspath $(dir $(lastword $(MAKEFILE_LIST))))

CLICK_DIR ?= $(THIS_DIR)/click
CLICK_BURST ?= 1

compile:
	@$(THIS_DIR)/setup.sh 2>/dev/null

run:
	@sudo $(CLICK_DIR)/bin/click burst=$(CLICK_BURST) --dpdk $(TN_ARGS) -- $(THIS_DIR)/$(TN_NF).click
