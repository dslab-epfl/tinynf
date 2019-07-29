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
# Warn on signed/unsigned conversion issues, as well as narrowing conversion issues
CFLAGS += -Wconversion
# Warn on unused macros
CFLAGS += -Wunused-macros
# Warn on non-static functions that do not have a prototype in a header
CFLAGS += -Wmissing-prototypes
# Warn on old-style function prototypes like foo() instead of foo(void)
CFLAGS += -Wstrict-prototypes
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
#CFLAGS += -O0 -g -rdynamic
CFLAGS += -DLOG_LEVEL=1
# Release flags
CFLAGS += -O3
# Linux-specific
CFLAGS += -D_GNU_SOURCE
CFLAGS += -lnuma

# TODO add https://kristerw.blogspot.com/2017/09/useful-gcc-warning-options-not-enabled.html once we get a more recent GCC

# TODO try the following for binary size (from https://stackoverflow.com/a/15314861/3311770)
# and check for impact on perf (esp. -Os)
# CFLAGS += -Os -ffunction-sections -fdata-sections -Wl,--gc-sections
# strip -s -R .comment -R .gnu.version --strip-unneeded
# and take a look at https://software.intel.com/en-us/blogs/2013/01/17/x86-gcc-code-size-optimizations

OUTPUT := tinynf

# Relative paths
CFLAGS += -I.
# Files
HEADERS := *.h os/*.h
FILES := *.c os/linux/*.c

$(OUTPUT): Makefile $(HEADERS) $(FILES)
	@rm -f *.gch $(OUTPUT)
	@$(CC) $(FILES) $(CFLAGS) -o $(OUTPUT)
