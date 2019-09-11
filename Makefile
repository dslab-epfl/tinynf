# Configuration
DEBUG := false
OS := linux
ARCH := x86
NET := 82599

# Toolchain
CC := clang-8 # clang has -Weverything, no need to manually list warnings we want; hardcode version for reproducibility
STRIP := strip

# Files
FILES := $(shell echo os/$(OS)/*.c arch/$(ARCH)/*.c net/$(NET)/*.c util/*.c)

# Main file
ifeq (,$(TN_VIGOR_NF))
FILES += tinynf.c
else
SHELL := /bin/bash -O extglob -O globstar -c
_IGNORED := $(shell cd deps/vigor/$(TN_VIGOR_NF) ; make autogen 2>/dev/null)
FILES += compat-vigor/main.c
FILES += $(shell echo deps/vigor/$(TN_VIGOR_NF)/!(loop).c)
CFLAGS += -I deps/vigor
CFLAGS += -isystem compat-vigor/dpdk
CFLAGS += -Wno-reserved-id-macro -Wno-sign-conversion -Wno-missing-prototypes -Wno-unused-parameter -Wno-unused-value -Wno-unused-function \
          -Wno-padded -Wno-tautological-unsigned-zero-compare -Wno-missing-variable-declarations -Wno-implicit-int-conversion -Wno-shorten-64-to-32 \
          -Wno-extra-semi-stmt -Wno-gnu-zero-variadic-macro-arguments
endif

# Required arguments
CFLAGS += -std=c17
CFLAGS += -Weverything
CFLAGS += -march=native
CFLAGS += -I . # Allow repo root relative paths
STRIPFLAGS := -R .comment

# Debug / release mode
ifeq ($(DEBUG),true)
STRIP := true # don't strip
CFLAGS += -O0 -g
CFLAGS += -DLOG_LEVEL=2
else
CFLAGS += -O3
CFLAGS += -DLOG_LEVEL=1
endif

# OS handling
ifeq ($(OS),linux)
CFLAGS += -D_GNU_SOURCE
LDFLAGS += -lnuma
endif

# Generate the dependencies in Makefile format using cc -M, then keep only the dependencies (not the targets:, not the backslashes for newlines)
tinynf: Makefile $(shell ${CC} ${FILES} $(CFLAGS) -M | sed 's/.*://g' | sed 's/\\//g')
	@$(CC) $(CFLAGS) $(FILES) -c
	@$(CC) $(LDFLAGS) $(subst .c,.o,$(notdir $(FILES))) -o $@
	@$(STRIP) $(STRIPFLAGS) $@
	@rm -f $(subst .c,.o,$(notdir $(FILES)))
