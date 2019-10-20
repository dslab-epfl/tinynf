# Configuration
DEBUG := false
OS := linux
ARCH := x86
NET := 82599
APP := tinynf

# Toolchain
CC := clang-8 # clang has -Weverything, no need to manually list warnings we want; hardcode version for reproducibility
STRIP := strip

# Files; only include our main file if we are not used by another makefile that already set FILES
DIR := $(abspath $(dir $(lastword $(MAKEFILE_LIST))))
ifeq (,$(FILES))
FILES := $(DIR)/tinynf.c
endif
FILES += $(shell echo $(DIR)/os/$(OS)/*.c $(DIR)/arch/$(ARCH)/*.c $(DIR)/net/$(NET)/*.c $(DIR)/util/*.c)

# Compiler and stripping args
CFLAGS += -std=c17
CFLAGS += -Weverything
CFLAGS += -march=native
CFLAGS += -I $(DIR)
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

# TODO proper dependency tracking...
.PHONY: default
default:
	@$(CC) $(CFLAGS) $(FILES) -c
	@$(CC) $(LDFLAGS) $(subst .c,.o,$(notdir $(FILES))) -o $(APP)
	@$(STRIP) $(STRIPFLAGS) $(APP)
	@rm -f $(subst .c,.o,$(notdir $(FILES)))
