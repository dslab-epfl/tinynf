# Configuration
DEBUG := false
ARCH := x86
OS := linux

# Toolchain
CC := clang-8 # clang has -Weverything, no need to manually list warnings we want; hardcode version for reproducibility
STRIP := strip

# Files
FILES := $(shell echo *.c os/$(OS)/*.c arch/$(ARCH)/*.c)

# Required arguments
CFLAGS += -std=c11 -D_POSIX_C_SOURCE=200809
CFLAGS += -Weverything
CFLAGS += -Wno-extra-semi-stmt # Allow macros to be used as if they were statements
CFLAGS += -I. # Allow repo root relative paths
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
CFLAGS += -Wno-format-nonliteral # We have format strings parameters; this warning is for potential security issues, we trust all code
endif

# Generate the dependencies in Makefile format using cc -M, then keep only the dependencies (not the targets:, not the backslashes for newlines)
tinynf: Makefile $(shell ${CC} ${FILES} $(CFLAGS) -M | sed 's/.*://g' | sed 's/\\//g')
	@$(CC) $(FILES) $(CFLAGS) -o $@
	@$(STRIP) $(STRIPFLAGS) $@
