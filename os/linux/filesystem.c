#include "os/linux/filesystem.h"

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


const char* tn_fs_readline(const char* path_format, ...)
{
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
	const char* fgets_result = fgets(line, LINE_SIZE, file);
	if (fgets_result == NULL) {
		free(line);
		return NULL;
	}

	return line;
}

uintptr_t tn_fs_mmap(const char* path_format, ...)
{
	va_list path_args;
	va_start(path_args, path_format);

	char path[PATH_SIZE];
	if (vsnprintf(path, PATH_SIZE, path_format, path_args) >= PATH_SIZE) {
		return (uintptr_t) -1;
	}

	const int fd = open(path, O_RDWR);
	if (fd == -1) {
		return (uintptr_t) -1;
	}

	struct stat stat;
	if (fstat(fd, &stat) == -1) {
		close(fd);
		return (uintptr_t) -1;
	}

	// TODO: See whether perf differs by mmapping this to a hugepage, or to a page right after the end of hugepages
	// Note that st_size is off_t, which is signed; let's make sure we don't accidentally convert a negative value to an unsigned...
	if (stat.st_size < 0) {
		close(fd);
		return (uintptr_t) -1;
	}
	const void* addr = mmap(NULL, (size_t) stat.st_size, PROT_READ | PROT_WRITE, MAP_SHARED, fd, 0);
	close(fd);
	if (addr == MAP_FAILED) {
		return (uintptr_t) -1;
	}

	return (uintptr_t) addr;
}
