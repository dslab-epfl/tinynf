CC ?= gcc

# C and POSIX versions
CFLAGS += -std=c11
CFLAGS += -D_POSIX_C_SOURCE=200809


# ---------------
# Enable warnings
# --------------

# All standard warnings
CFLAGS += -Wall -Wextra
# ISO compliance
CFLAGS += -pedantic -pedantic-errors
# Signed/unsigned conversion issues, as well as narrowing conversion issues
CFLAGS += -Wconversion

# Files
FILES := *.c

all:
	$(CC) $(CFLAGS) $(FILES)

clean:
	rm *.gch
