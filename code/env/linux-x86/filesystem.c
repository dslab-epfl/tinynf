#include "filesystem.h"

#include "util/log.h"

#include <stdarg.h>
#include <stdio.h>


// Should be big enough
#define PATH_SIZE 1024


bool tn_fs_readline(char* line, int line_size, const char* path_format, ...)
{
	va_list path_args;
	va_start(path_args, path_format);
	FILE* file = NULL;
	char* fgets_result = NULL;

	char path[PATH_SIZE];
	if (vsnprintf(path, PATH_SIZE, path_format, path_args) >= PATH_SIZE) {
		TN_DEBUG("Couldn't format the path to read a line from");
		goto error;
	}

	file = fopen(path, "r");
	if (file == NULL) {
		TN_DEBUG("Couldn't open the path to read a line from");
		goto error;
	}

	fgets_result = fgets(line, line_size, file);
	if (fgets_result == NULL) {
		TN_DEBUG("Couldn't read a line");
		goto error;
	}

	va_end(path_args);
	fclose(file);
	return true;

error:
	va_end(path_args);
	if (file != NULL) {
		fclose(file);
	}
	return false;
}
