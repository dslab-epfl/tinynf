#pragma once

#if LOG_LEVEL > 0
#include <stdio.h>

// Include this here so that logging can use PRIu32 and friends
#include <inttypes.h>

#define TN_PRINT(categ, ...) fprintf(stderr, "[%s] ", #categ); fprintf(stderr, __VA_ARGS__); fprintf(stderr, "\n"); fflush(stderr)
#endif

#if LOG_LEVEL >= 2
#define TN_DEBUG(...) TN_PRINT(DEBUG, __VA_ARGS__)
#else
#define TN_DEBUG(...)
#endif

#if LOG_LEVEL >= 1
#define TN_INFO(...) TN_PRINT(INFO, __VA_ARGS__)
#else
#define TN_INFO(...)
#endif
