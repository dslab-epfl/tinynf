#include "filesystem.h"

#include <stdarg.h>
#include <stdlib.h>
#include <stdio.h>

char* tn_fs_readline(char* path_format, ...)
{
	// hopefully they should be big enough
	const int PATH_SIZE = 1024;
	const int LINE_SIZE = 1024;

	va_list path_args;
	va_start(path_args, path_format);

	char path[PATH_SIZE];
	if (vsnprintf(path, PATH_SIZE, path_format, path_args) >= PATH_SIZE) {
		return NULL;
	}

	FILE* file = fopen(path, "r");
	if (file == NULL) {
		return NULL;
	}

	char* line = (char*) malloc(LINE_SIZE);
	char* fgets_result = fgets(line, LINE_SIZE, file);
	if (fgets_result == NULL) {
		free(line);
		return NULL;
	}

	return line;
}
