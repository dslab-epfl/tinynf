#pragma once

#include <stdint.h>

// Reads a single line from the file at the given path, or returns NULL if this is not possible.
// The file can have printf-style placeholders, in which case additional arguments must be passed.
// It is the caller's responsibility to free the memory returned by this function.
const char* tn_fs_readline(const char* path_format, ...);

// Memory-maps the file at the given path, or returns NULL if this is not possible.
uintptr_t tn_fs_mmap(const char* path_format, ...);
