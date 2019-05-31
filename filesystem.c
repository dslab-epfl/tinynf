#include "filesystem.h"

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


char* tn_fs_readline(char* path_format, ...)
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
	char* fgets_result = fgets(line, LINE_SIZE, file);
	if (fgets_result == NULL) {
		free(line);
		return NULL;
	}

	return line;
}

void* tn_fs_mmap(char* path_format, ...)
{
	va_list path_args;
	va_start(path_args, path_format);

	char path[PATH_SIZE];
	if (vsnprintf(path, PATH_SIZE, path_format, path_args) >= PATH_SIZE) {
		return NULL;
	}

        int fd = open(path, O_RDWR);
        if (fd == -1) {
                return NULL;
        }

	struct stat stat;
	if (fstat(fd, &stat) == -1) {
		close(fd);
		return NULL;
	}

        // TODO: See whether perf differs by mmapping this to a hugepage, or to a page right after the end of hugepages
        void* addr = mmap(NULL, stat.st_size, PROT_READ | PROT_WRITE, MAP_SHARED, fd, 0);
        close(fd);

        if (addr == MAP_FAILED) {
                return NULL;
        }

	// Should not happen but technically permitted by the mmap interface
	if (addr == NULL) {
		munmap(addr, stat.st_size);
		return NULL;
	}

	return addr;
}
