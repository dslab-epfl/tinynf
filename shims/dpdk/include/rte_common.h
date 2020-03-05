#pragma once

#include <stdarg.h>
#include <stdio.h>
#include <stdlib.h>


static inline void rte_exit(int exit_code, const char *format, ...)
{
	va_list args;
	va_start(args, format);
	vfprintf(stderr, format, args);
	va_end(args);
	exit(exit_code);
}
