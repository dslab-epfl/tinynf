# Configuration
DEBUG := false
OS := linux
ARCH := x86
NET := 82599

# Toolchain
CC := clang-8 # clang has -Weverything, no need to manually list warnings we want; hardcode version for reproducibility
STRIP := strip

# Files
FILES := $(shell echo *.c os/$(OS)/*.c arch/$(ARCH)/*.c net/$(NET)/*.c util/*.c)

# Required arguments
CFLAGS += -std=c17
CFLAGS += -Weverything
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
LDFLAGS += -lnuma
endif

# Generate the dependencies in Makefile format using cc -M, then keep only the dependencies (not the targets:, not the backslashes for newlines)
tinynf: Makefile $(shell ${CC} ${FILES} $(CFLAGS) -M | sed 's/.*://g' | sed 's/\\//g')
	@$(CC) $(CFLAGS) $(FILES) -c
	@$(CC) $(LDFLAGS) $(subst .c,.o,$(notdir $(FILES))) -o $@
	@$(STRIP) $(STRIPFLAGS) $@
	@rm -f $(subst .c,.o,$(notdir $(FILES)))
