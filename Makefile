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
# Debug flags
CFLAGS += -O0 -g -rdynamic -DLOG_LEVEL=2

OUTPUT := tinynf

# Files
FILES := *.c

all:
	$(CC) $(CFLAGS) $(FILES) -o $(OUTPUT)

clean:
	rm -f *.gch $(OUTPUT)
