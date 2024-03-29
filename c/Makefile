# This Makefile expects to be included in all kinds of contexts, such as in "shim" layers.
# Thus, it does not use any of the standard variable names such as "CC" to avoid conflicts.
# Instead, every variable name is prefixed by TN_.
# Targets:
# - Default target to compile
# Overrideable variables:
# - TN_DEBUG, default 1, debug level (0 = no output, 1 = info, 2 = debug, 3 = verbose); if > 1, code will be compiled with debug symbols
# - TN_ENV, default 'linux-x86', environment to use (folder in env/)
# - TN_APP, default 'tinynf', app name when compiled
# - TN_CC, default cc, compiler to use
# Appendable variables:
# - TN_FILES, defaults to all TinyNF files, files to compile
# - TN_CFLAGS, defaults making sense for TinyNF, compilation and linking flags to use
# Special behavior when TN_FILES is not set:
# - The "main" TinyNF file is included in compilation
# - Compiler warnings are enabled
# Special behavior when the variable TN_NO_DEFAULT_TARGET is set:
# - The default target is not defined

# Current directory
TN_DIR := $(abspath $(dir $(lastword $(MAKEFILE_LIST))))

# Defaults
TN_DEBUG ?= 1
TN_CC ?= cc
TN_APP ?= tinynf
TN_ENV ?= $(TN_DIR)/env/linux-x86
TN_MODE ?= restricted

ifneq (,$(findstring clang,$(TN_CC)))
# Ignore cast warnings, we know what we're doing
# Also ignore unused CLI args, this triggers due to -rdynamic in debug mode
# And packing/padding warnings for stuff like "you don't need to explicitly say this struct should be packed"
# And the weird declaration-after-statement that tells you about pre-C99 compat even if you don't like it
TN_CFLAGS += -Weverything -Wno-cast-qual -Wno-cast-align -Wno-unused-command-line-argument -Wno-packed -Wno-padded -Wno-declaration-after-statement
endif
ifneq (,$(findstring gcc,$(TN_CC)))
TN_CFLAGS += -Wall -Wextra -Wshadow -Wstrict-aliasing -Wunused-macros -pedantic
# GCC tends to use 'cmov' instructions otherwise, which have utterly terrible tail latency on some machines
# (this is an optimization copied from Vigor)
TN_CFLAGS += -fno-if-conversion -fno-if-conversion2
endif

# Files
TN_FILES := $(TN_DIR)/main.c
TN_FILES += $(shell echo $(TN_ENV)/*.c)

# Compiler args
TN_CFLAGS += -std=c11
TN_CFLAGS += -march=native
TN_CFLAGS += -flto
TN_CFLAGS += -I $(TN_DIR)
TN_CFLAGS += -DLOG_LEVEL=$(TN_DEBUG)

ifeq ($(TN_MODE),flexible)
TN_CFLAGS += -DTN_MODE=2
else ifeq ($(TN_MODE),const)
TN_CFLAGS += -DTN_MODE=1
else
TN_CFLAGS += -DTN_MODE=0
endif

# Debug mode if level > 1 (i.e. not just 'info')
ifeq ($(shell test $(TN_DEBUG) -gt 1; echo $$?),0)
TN_CFLAGS += -O0 -g -rdynamic
else
TN_CFLAGS += -O3
endif

# Linux-only compiler flags
ifeq ($(TN_DIR)/env/linux-x86,$(TN_ENV))
TN_CFLAGS += -D_DEFAULT_SOURCE # for MAP_* constants and the syscall function
endif

# Always rebuild since the flags might have changed
.PHONY: build
build:
	@$(TN_CC) $(TN_CFLAGS) $(TN_FILES) -o $(TN_APP)

format:
	@find . -regex '.*\.[ch]' -exec clang-format -i {} \;
