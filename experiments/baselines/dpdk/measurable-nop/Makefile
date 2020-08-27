# Get current dir, see https://stackoverflow.com/a/8080530
SELF_DIR := $(abspath $(dir $(lastword $(MAKEFILE_LIST))))

RTE_SDK := $(SELF_DIR)/../dpdk
RTE_TARGET := x86_64-native-linuxapp-gcc

# DPDK stuff, part 1
include $(RTE_SDK)/mk/rte.vars.mk

CFLAGS += -I $(SELF_DIR)/../../../code

SRCS-y += main.c

APP := nf

# DPDK stuff, part 2
include $(RTE_SDK)/mk/rte.extapp.mk
