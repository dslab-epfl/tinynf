# This Makefile expects to be included in all kinds of contexts, such as in "shim" layers.
# Thus, it does not use any of the standard variable names such as "CC" to avoid conflicts.
# Instead, every variable name is prefixed by TN_.
# Targets:
# - Default target to compile
# Overrideable variables:
# - TN_DEBUG, default 1, debug level (0 = no output, 1 = info, 2 = debug, 3 = verbose); if > 1, code will be compiled with debug symbols
# - TN_ENV, default 'linux-x86', environment to use (folder in env/)
# - TN_NET, default '82599', network driver to use (folder in net/)
# - TN_APP, default 'tinynf', app name when compiled
# - TN_CC, default undocumented, compiler to use
# Appendable variables:
# - TN_FILES, defaults to all TinyNF files, files to compile
# - TN_CFLAGS, defaults making sense for TinyNF, compilation and linking flags to use
# Special behavior when TN_FILES is not set:
# - The "main" TinyNF file is included in compilation
# - Compiler warnings are enabled
# Special behavior when the variable TN_NO_DEFAULT_TARGET is set:
# - The default target is not defined

# Defaults
TN_DEBUG ?= 1
TN_ENV ?= linux-x86
TN_NET ?= 82599
TN_APP ?= tinynf
TN_CC ?= gcc

# Current directory
TN_DIR := $(abspath $(dir $(lastword $(MAKEFILE_LIST))))

# Special behavior when TN_FILES is not set
ifeq (,$(TN_FILES))
TN_FILES := $(TN_DIR)/tinynf.c
ifneq (,$(findstring clang,$(TN_CC)))
TN_CFLAGS += -Weverything
endif
ifneq (,$(findstring gcc,$(TN_CC)))
TN_CFLAGS += -Wall -Wextra -Wshadow -Wstrict-aliasing -Wunused-macros -pedantic
# GCC tends to use 'cmov' instructions otherwise, which have utterly terrible tail latency on some machines
# (this is an optimization copied from Vigor)
TN_CFLAGS += -fno-if-conversion -fno-if-conversion2
endif
endif

# Files
TN_FILES += $(shell echo $(TN_DIR)/env/$(TN_ENV)/*.c $(TN_DIR)/net/$(TN_NET)/*.c)

# Compiler args
TN_CFLAGS += -std=c11
TN_CFLAGS += -march=native
TN_CFLAGS += -I $(TN_DIR)
TN_CFLAGS += -DLOG_LEVEL=$(TN_DEBUG)

# Debug mode if level > 1 (i.e. not just 'info')
ifeq ($(shell test $(TN_DEBUG) -gt 1; echo $$?),0)
TN_CFLAGS += -O0 -g
else
TN_CFLAGS += -O3
endif

# Linux-only compiler flags
ifeq (linux-x86,$(TN_ENV))
TN_CFLAGS += -D_DEFAULT_SOURCE # for MAP_* constants and the syscall function
endif

ifndef TN_NO_DEFAULT_TARGET
.PHONY: tn_default
tn_default:
	@$(TN_CC) $(TN_CFLAGS) $(TN_FILES) -c
	@$(TN_CC) $(subst .c,.o,$(notdir $(TN_FILES))) $(TN_CFLAGS) -o $(TN_APP)
	@rm -f $(subst .c,.o,$(notdir $(TN_FILES)))
endif
