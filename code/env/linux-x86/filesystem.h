#pragma once

#include <stdbool.h>


// Reads a single line from the file at the given path, or returns false.
// The file can have printf-style placeholders, in which case additional arguments must be passed.
// It is the caller's responsibility to free the memory returned by this function.
__attribute__((format(printf, 2, 3)))
bool tn_fs_readline(char** out_line, const char* path_format, ...);
