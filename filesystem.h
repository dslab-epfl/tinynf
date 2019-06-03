#pragma once

#include <stdint.h>

// Reads a single line from the file at the given path, or returns NULL if this is not possible.
// The file can have printf-style placeholders, in which case additional arguments must be passed.
// It is the caller's responsibility to free the memory returned by this function.
char* tn_fs_readline(char* path_format, ...);

// Memory-maps the file at the given path, or returns NULL if this is not possible.
void* tn_fs_mmap(char* path_format, ...);
