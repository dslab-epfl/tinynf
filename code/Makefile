# This Makefile expects to be included in all kinds of contexts, such as in "shim" layers.
# Thus, it does not use any of the standard variable names such as "CC" to avoid conflicts.
# Instead, every variable name is prefixed by TN_.
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
# - The default target is not defined

# Configuration
TN_DEBUG ?= 1
TN_ENV ?= linux-x86
TN_NET ?= 82599
TN_APP ?= tinynf

# Toolchain
TN_CC ?= clang-9 # clang has -Weverything, no need to manually list warnings we want; hardcode version for reproducibility
TN_STRIP ?= strip

# Files
TN_DIR := $(abspath $(dir $(lastword $(MAKEFILE_LIST))))
ifeq (,$(TN_FILES))
TN_FILES := $(TN_DIR)/tinynf.c
TN_CFLAGS += -Weverything
endif
TN_FILES += $(shell echo $(TN_DIR)/env/$(TN_ENV)/*.c $(TN_DIR)/net/$(TN_NET)/*.c $(TN_DIR)/util/*.c)

# Compiler and stripping args
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

# Per-environment config
ifeq ($(TN_ENV),linux-x86)
TN_CFLAGS += -D_GNU_SOURCE
TN_LDFLAGS += -lnuma
endif

ifndef TN_NO_DEFAULT_TARGET
# TODO proper dependency tracking...
.PHONY: tn_default
tn_default:
	@$(TN_CC) $(TN_CFLAGS) $(TN_FILES) -c
	@$(TN_CC) $(subst .c,.o,$(notdir $(TN_FILES))) $(TN_LDFLAGS) -o $(TN_APP)
	@$(TN_STRIP) $(TN_STRIPFLAGS) $(TN_APP)
	@rm -f $(subst .c,.o,$(notdir $(TN_FILES)))

# just so it can be run with the benchmark scripts
run:
	sudo ./tinynf $(TN_ARGS)
endif
