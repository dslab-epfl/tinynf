CC ?= gcc

# C and POSIX versions
CFLAGS += -std=c11
CFLAGS += -D_POSIX_C_SOURCE=200809

# Enable warnings
CFLAGS += -Wall
CFLAGS += -Wextra
CFLAGS += -Wpedantic
CFLAGS += -pedantic-errors

# Files
FILES := *.c

all:
	$(CC) $(CFLAGS) $(FILES)

clean:
	rm *.gch
