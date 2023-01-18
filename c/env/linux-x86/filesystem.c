#include "filesystem.h"

#include "util/log.h"

#include <fcntl.h>
#include <stdarg.h>
#include <stdio.h>
#include <unistd.h>

// Should be big enough
#define PATH_SIZE 1024

bool tn_fs_readline(char* line, unsigned line_size, const char* path_format, ...)
{
	va_list path_args;
	va_start(path_args, path_format);
	int fd = -1;
	long read_result = -1;

	char path[PATH_SIZE];
	if (vsnprintf(path, PATH_SIZE, path_format, path_args) >= PATH_SIZE) {
		TN_DEBUG("Couldn't format the path to read a line from");
		goto error;
	}

	fd = open(path, O_RDONLY);
	if (fd == -1) {
		TN_DEBUG("Couldn't open the path to read a line from");
		goto error;
	}

	read_result = read(fd, line, line_size);
	if (read_result == -1) {
		TN_DEBUG("Couldn't read a line");
		goto error;
	}

	va_end(path_args);
	close(fd);
	return true;

error:
	va_end(path_args);
	if (fd != -1) {
		close(fd);
	}
	return false;
}
