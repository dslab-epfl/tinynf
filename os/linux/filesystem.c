#include "os/linux/filesystem.h"

#include "util/log.h"

#include <fcntl.h>
#include <stdarg.h>
#include <stdlib.h>
#include <stdio.h>
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

	char path[PATH_SIZE];
	if (vsnprintf(path, PATH_SIZE, path_format, path_args) >= PATH_SIZE) {
		TN_DEBUG("Couldn't format the path to read a line from");
		return false;
	}

	FILE* file = fopen(path, "r");
	if (file == NULL) {
		TN_DEBUG("Couldn't open the path to read a line from");
		return false;
	}

	char* line = (char*) malloc(LINE_SIZE);
	const char* fgets_result = fgets(line, LINE_SIZE, file);
	if (fgets_result == NULL) {
		TN_DEBUG("Couldn't read a line");
		free(line);
		return false;
	}

	*out_line = line;
	return true;
}

bool tn_fs_mmap(uintptr_t* out_addr, const char* path_format, ...)
{
	va_list path_args;
	va_start(path_args, path_format);

	char path[PATH_SIZE];
	if (vsnprintf(path, PATH_SIZE, path_format, path_args) >= PATH_SIZE) {
		TN_DEBUG("Couldn't format the path to mmap");
		return false;
	}

	const int fd = open(path, O_RDWR);
	if (fd == -1) {
		TN_DEBUG("Couldn't open the file to mmap");
		return false;
	}

	struct stat stat;
	if (fstat(fd, &stat) == -1) {
		TN_DEBUG("Couldn't stat the file to mmap");
		close(fd);
		return false;
	}

	// Note that st_size is off_t, which is signed; let's make sure we don't accidentally convert a negative value to an unsigned...
	if (stat.st_size < 0) {
		TN_DEBUG("The file to mmap has a negative size");
		close(fd);
		return false;
	}
	const void* addr = mmap(NULL, (size_t) stat.st_size, PROT_READ | PROT_WRITE, MAP_SHARED, fd, 0);
	close(fd);
	if (addr == MAP_FAILED) {
		TN_DEBUG("Mmap failed");
		return false;
	}

	*out_addr = (uintptr_t) addr;
	return true;
}
