# --------------------------------------------------------
# C compiler, language version, POSIX version and warnings
# --------------------------------------------------------
# GCC
CC ?= gcc
# C11
CFLAGS += -std=c11
# POSIX-2008
CFLAGS += -D_POSIX_C_SOURCE=200809
# All standard warnings
CFLAGS += -Wall -Wextra
# ISO compliance
CFLAGS += -pedantic -pedantic-errors
# Signed/unsigned conversion issues, as well as narrowing conversion issues
CFLAGS += -Wconversion
# Warn on unsafe pointer casts
CFLAGS += -Wcast-qual
# Warn on pointer casts that require alignment changes
# TODO: Add '=strict' once we move to a GCC version that supports it
CFLAGS += -Wcast-align
# Warn on multiple decls in the same scope, even if it's legal
CFLAGS += -Wredundant-decls
# Warn on shadowing
CFLAGS += -Wshadow
# Give string constants the 'const char[]' type to catch writes to them
CFLAGS += -Wwrite-strings
# Warn if a requested inline cannot be performed
CFLAGS += -Winline
# Warn if a struct is requested to be packed but this has no effect
CFLAGS += -Wpacked
# Warn if a struct is padded
CFLAGS += -Wpadded
# Warn if a user-supplied include dir does not exist
CFLAGS += -Wmissing-include-dirs
# Warn if a loop cannot be optimized because of a lack of information
CFLAGS += -Wunsafe-loop-optimizations
# Warn if GCC bails out on an optimization
CFLAGS += -Wdisabled-optimization
# Warn on code that wouldn't compile under C++
CFLAGS += -Wc++-compat
# Debug flags
#CFLAGS += -O0 -g -rdynamic -DLOG_LEVEL=2
# Release flags
CFLAGS += -O2

OUTPUT := tinynf

# Files
FILES := *.c

all:
	$(CC) $(CFLAGS) $(FILES) -o $(OUTPUT)

clean:
	rm -f *.gch $(OUTPUT)
