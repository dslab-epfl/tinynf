#include "os/linux/filesystem.h"

#include "util/log.h"

#include <fcntl.h>
#include <stdarg.h>
#include <stdio.h>
#include <stdlib.h>
#include <unistd.h>

#include <sys/mman.h>
#include <sys/stat.h>


// Should be big enough
#define PATH_SIZE 1024
#define LINE_SIZE 1024


bool tn_fs_readline(char** out_line, const char* path_format, ...)
{
	va_list path_args;
	va_start(path_args, path_format);
	FILE* file = NULL;
	char* line = NULL;

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

	line = (char*) calloc(LINE_SIZE, sizeof(char));
	const char* fgets_result = fgets(line, LINE_SIZE, file);
	if (fgets_result == NULL) {
		TN_DEBUG("Couldn't read a line");
		goto error;
	}

	va_end(path_args);
	fclose(file);
	*out_line = line;
	return true;

error:
	va_end(path_args);
	if (file != NULL) {
		fclose(file);
	}
	free(line);
	return false;
}

bool tn_fs_mmap(uintptr_t* out_addr, const char* path_format, ...)
{
	va_list path_args;
	va_start(path_args, path_format);
	int fd = -1;

	char path[PATH_SIZE];
	if (vsnprintf(path, PATH_SIZE, path_format, path_args) >= PATH_SIZE) {
		TN_DEBUG("Couldn't format the path to mmap");
		goto error;
	}

	fd = open(path, O_RDWR);
	if (fd == -1) {
		TN_DEBUG("Couldn't open the file to mmap");
		goto error;
	}

	struct stat stat;
	if (fstat(fd, &stat) == -1) {
		TN_DEBUG("Couldn't stat the file to mmap");
		goto error;
	}

	// Note that st_size is off_t, which is signed; let's make sure we don't accidentally convert a negative value to an unsigned...
	if (stat.st_size < 0) {
		TN_DEBUG("The file to mmap has a negative size");
		goto error;
	}
	const void* addr = mmap(NULL, (size_t) stat.st_size, PROT_READ | PROT_WRITE, MAP_SHARED, fd, 0);
	if (addr == MAP_FAILED) {
		TN_DEBUG("Mmap failed");
		goto error;
	}

	va_end(path_args);
	close(fd);
	*out_addr = (uintptr_t) addr;
	return true;

error:
	va_end(path_args);
	if (fd != 1) {
		close(fd);
	}
	return false;
}
