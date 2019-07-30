#pragma once

#if LOG_LEVEL > 0
#include <stdio.h>

// Include this here so that logging can use PRIu32 and friends
#include <inttypes.h>

#define _TN_PRINT(categ, ...) fprintf(stderr, "[%5s] ", #categ); fprintf(stderr, __VA_ARGS__); fprintf(stderr, "\n"); fflush(stderr);
#endif

#if LOG_LEVEL >= 2
#define TN_DEBUG(...) _TN_PRINT(DEBUG, __VA_ARGS__)
#else
#define TN_DEBUG(...)
#endif

#if LOG_LEVEL >= 1
#define TN_INFO(...) _TN_PRINT(INFO, __VA_ARGS__)
#else
#define TN_INFO(...)
#endif
