ifndef TN_NF
$(error Please define TN_NF to a Vigor NF without the vig prefix, e.g. 'nat')
endif

VIGOR_DIR := $(abspath $(dir $(lastword $(MAKEFILE_LIST))))/../vigor

compile:
	@# Nothing!


ifeq ($(RTE_TARGET),.)
# Our own DPDK shim - not much to do beyond ensuring the compiler and loader are what they need to be
run:
	@NF_DPDK_ARGS="$(TN_ARGS)" LD=cc TN_CC=cc make -C $(VIGOR_DIR)/vig$(TN_NF) run
else
# Always make DPDK in case Linux got updated, reinstall the kernel module and re-bind the devices just to be sure
run:
	@sudo rmmod igb_uio 2>/dev/null || true
	@make -C $(RTE_SDK) install -j$$(nproc) T=x86_64-native-linuxapp-gcc DESTDIR=. >/dev/null 2>&1
	@sudo insmod $(RTE_SDK)/$(RTE_TARGET)/kmod/igb_uio.ko
	@sudo $(RTE_SDK)/usertools/dpdk-devbind.py -u $(TN_ARGS) >/dev/null 2>&1
	@sudo $(RTE_SDK)/usertools/dpdk-devbind.py -b igb_uio $(TN_ARGS)
	@make -C $(VIGOR_DIR)/vig$(TN_NF) run
endif
