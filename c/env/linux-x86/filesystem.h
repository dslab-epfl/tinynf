// Filesystem abstraction, internal to the linux environment abstraction.

#pragma once

#include <stdbool.h>


// Reads a single line from the file at the given path into the given line, reading at most line_size characters, or returns false.
// The file can have printf-style placeholders, in which case additional arguments must be passed.
__attribute__((format(printf, 3, 4)))
bool tn_fs_readline(char* line, unsigned line_size, const char* path_format, ...);
