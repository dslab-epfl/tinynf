# This Makefile expects to be included in all kinds of contexts, such as in "shim" layers.
# Thus, it does not use any of the standard variable names such as "CC" to avoid conflicts.
# Instead, every variable name is prefixed by TN_.
# Targets:
# - Default target to compile
# - 'run' target to run
# Overrideable variables:
# - TN_DEBUG, default 1, debug level (0 = no output, 1 = info, 2 = debug, 3 = verbose); if > 1, code will be compiled with debug symbols
# - TN_ENV, default 'linux-x86', environment to use (folder in env/)
# - TN_NET, default '82599', network driver to use (folder in net/)
# - TN_APP, default 'tinynf', app name when compiled
# - TN_CC, default undocumented, compiler to use
# - TN_STRIP, default undocumented, stripper to use
# Appendable variables:
# - TN_FILES, defaults to all TinyNF files, files to compile
# - TN_CFLAGS, defaults making sense for TinyNF, compilation flags to use
# - TN_LDFLAGS, defaults making sense for TinyNF, loader flags to use
# - TN_STRIPFLAGS, defaults making sense for TinyNF, stripper flags to use
# Special behavior when TN_FILES is not set:
# - The "main" TinyNF file is included in compilation
# - Compiler warnings are enabled
# Special behavior when the variable TN_NO_DEFAULT_TARGET is set:
# - The default and run targets are not defined

# Configuration
TN_DEBUG ?= 1
TN_ENV ?= linux-x86
TN_NET ?= 82599
TN_APP ?= tinynf

# Toolchain
TN_CC ?= gcc-9 # hardcode version for reproducibility
TN_STRIP ?= strip

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
endif
endif

# Files
TN_FILES += $(shell echo $(TN_DIR)/env/$(TN_ENV)/*.c $(TN_DIR)/net/$(TN_NET)/*.c)

# Compiler and stripping args
TN_CFLAGS += -std=c11
TN_CFLAGS += -march=native
TN_CFLAGS += -I $(TN_DIR)
TN_CFLAGS += -DLOG_LEVEL=$(TN_DEBUG)
TN_STRIPFLAGS += -R .comment

# Debug mode if level > 1 (i.e. not just 'info')
ifeq ($(shell test $(TN_DEBUG) -gt 1; echo $$?),0)
TN_STRIP := true # don't strip
TN_CFLAGS += -O0 -g
else
TN_CFLAGS += -O3
endif

# Linux-only compiler flags
ifeq (linux-x86,$(TN_ENV))
TN_CFLAGS += -D_POSIX_C_SOURCE=200809L -D_GNU_SOURCE
endif

ifndef TN_NO_DEFAULT_TARGET
.PHONY: tn_default
tn_default:
	@$(TN_CC) $(TN_CFLAGS) $(TN_FILES) -c
	@$(TN_CC) $(subst .c,.o,$(notdir $(TN_FILES))) $(TN_LDFLAGS) -o $(TN_APP)
	@$(TN_STRIP) $(TN_STRIPFLAGS) $(TN_APP)
	@rm -f $(subst .c,.o,$(notdir $(TN_FILES)))

run:
	@sudo ./tinynf $(TN_ARGS)
endif
