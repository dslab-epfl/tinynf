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
# Allow the use of special patterns in shell, as Vigor does
SHELL := /bin/bash -O extglob -c
# Force the auto-generation of Vigor files
_IGNORED := $(shell cd deps/vigor/$(TN_VIGOR_NF) ; make autogen 2>/dev/null)
# Our main stub
FILES += compat-vigor/main.c
# Vigor NF files; don't include the loop file, Vigor only uses it during verification
FILES += $(shell echo deps/vigor/$(TN_VIGOR_NF)/!(loop).c)
# Vigor's libVig; boilerplate-assumptions is a stub file for builtins
FILES += $(shell echo deps/vigor/libvig/verified/!(boilerplate-assumptions).c)
# Vigor utility files
FILES += deps/vigor/nf-util.c
# Vigor expects its root dir to be an include path
CFLAGS += -I deps/vigor
# Our DPDK stub headers
CFLAGS += -isystem compat-vigor/dpdk
# Vigor compiles with DPDK makefiles, which do not care about all those...
CFLAGS += -Wno-reserved-id-macro -Wno-sign-conversion -Wno-missing-prototypes -Wno-unused-parameter -Wno-unused-value -Wno-unused-function \
          -Wno-padded -Wno-tautological-unsigned-zero-compare -Wno-missing-variable-declarations -Wno-implicit-int-conversion -Wno-shorten-64-to-32 \
          -Wno-extra-semi-stmt -Wno-gnu-zero-variadic-macro-arguments -Wno-empty-translation-unit -Wno-newline-eof -Wno-unused-variable
# And the same trick Vigor uses to pass args to the NFOS
DQUOTE := \"
SPACE := $(null) #
COMMA := ,
CFLAGS += -DVIGOR_ARGS=\"$(subst $(SPACE),$(DQUOTE)$(COMMA)$(DQUOTE),$(TN_VIGOR_NF) $(TN_VIGOR_ARGS))\"
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
