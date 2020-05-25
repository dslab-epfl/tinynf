// Performance debugging utilities.
// Only enabled if `TN_DEBUG_PERF` is defined; if so, it acts as the number of 10K packet batches to record before shutting down.
// If enabled, link with libPAPI: https://icl.utk.edu/papi/

#pragma once

#ifdef TN_DEBUG_PERF
#include "papi.h"
#include <stdio.h>
#include <stdlib.h>

static int papi_events[] = {PAPI_TOT_CYC, PAPI_TOT_INS, PAPI_L1_DCM, PAPI_L1_ICM, PAPI_L2_TCM, PAPI_L3_TCM};
#define papi_events_count sizeof(papi_events)/sizeof(papi_events[0])
static uint64_t papi_counter;
static uint8_t papi_batches[TN_DEBUG_PERF];
static long long papi_values[TN_DEBUG_PERF][papi_events_count];

// PAPI functions: call START(), then RESET() before your event and RECORD() immediately after
#define TN_PERF_PAPI_START() do { \
		printf("Counters: cycles, instructions, L1d, L1i, L2, L3\n"); \
		if (PAPI_start_counters(papi_events, papi_events_count) != PAPI_OK) { \
			printf("Couldn't start PAPI counters!\n"); \
			exit(1); \
		} \
	} while(0)
#define TN_PERF_PAPI_RESET() do { PAPI_read_counters(papi_values[papi_counter], papi_events_count); } while(0)
#define TN_PERF_PAPI_RECORD(batch_count) do { \
		PAPI_read_counters(papi_values[papi_counter], papi_events_count); \
		papi_batches[papi_counter] = batch_count; \
		papi_counter += batch_count; \
		if (papi_counter >= TN_DEBUG_PERF) { \
			for (uint64_t n = 0; n < TN_DEBUG_PERF; n++) { \
				uint64_t m; \
				for (m = 0; m < papi_batches[n] && n + m < TN_DEBUG_PERF; m++) { \
					for (uint64_t e = 0; e < papi_events_count; e++) { \
						printf("%lf ", (double) papi_values[n][e] / (double) papi_batches[n]); \
					} \
					printf("\n"); \
				} \
				n += m - 1; \
			} \
			exit(0); \
		} \
	} while(0)
#else
#define TN_PERF_PAPI_START()
#define TN_PERF_PAPI_RESET()
#define TN_PERF_PAPI_RECORD(...)
#endif
