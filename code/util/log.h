// Logging utilities.
// There are 4 log levels:
// - 0: No logging at all
// - 1: Logging important information, like "initialization complete"
// - 2: Logging debugging information, like "some operation failed, although the overall system may be fine"
// - 3: Logging everything, like "wrote value 0xAB to register CD of device 3"

#pragma once

#if LOG_LEVEL > 0
#include <stdio.h>

// Include this here so that logging can use format specifiers for fixed-size integers, e.g. "PRIu32" for uint32_t
#include <inttypes.h>

#define TN_PRINT(categ, ...) do { fprintf(stderr, "[%s] ", #categ); fprintf(stderr, __VA_ARGS__); fprintf(stderr, "\n"); fflush(stderr); } while(0)
#endif

#if LOG_LEVEL >= 3
#define TN_VERBOSE(...) TN_PRINT(VERBOSE, __VA_ARGS__)
#else
#define TN_VERBOSE(...)
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
