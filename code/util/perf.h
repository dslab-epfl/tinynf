#pragma once

#ifdef TN_DEBUG_PERF
#include "papi.h"
#include <stdio.h>
#include <stdlib.h>

static int papi_events[] = {PAPI_TOT_CYC, PAPI_TOT_INS, PAPI_L1_DCM, PAPI_L1_ICM, PAPI_L2_TCM, PAPI_L3_TCM};
static uint64_t papi_counter;
static uint64_t papi_batch_counter;
#define papi_events_count sizeof(papi_events)/sizeof(papi_events[0])
#define TN_PERF_PAPI_BATCH_SIZE 10000
static long long papi_values[TN_PERF_PAPI_BATCH_SIZE][papi_events_count];

// PAPI functions: call START(), then RESET() before your event and RECORD() immediately after
#define TN_PERF_PAPI_START() do { \
		printf("Counters: cycles, instructions, L1d, L1i, L2, L3\n"); \
		if (PAPI_start_counters(papi_events, papi_events_count) != PAPI_OK) { \
			printf("Couldn't start PAPI counters!\n"); \
			exit(1); \
		} \
	} while(0)
#define TN_PERF_PAPI_RESET() do { PAPI_read_counters(papi_values[papi_counter], papi_events_count); } while(0)
#define TN_PERF_PAPI_RECORD() do { \
		PAPI_read_counters(papi_values[papi_counter], papi_events_count); \
		papi_counter++; \
		if (papi_counter == TN_PERF_PAPI_BATCH_SIZE) { \
			for (uint64_t n = 0; n < TN_PERF_PAPI_BATCH_SIZE; n++) { \
				for (uint64_t e = 0; e < papi_events_count; e++) { \
					printf("%lld ", papi_values[n][e]); \
				} \
				printf("\n"); \
			} \
			papi_counter = 0; \
			papi_batch_counter++; \
			if (papi_batch_counter == TN_DEBUG_PERF) { \
				exit(0); \
			} \
		} \
	} while(0)
#else
#define TN_PERF_PAPI_START()
#define TN_PERF_PAPI_RESET()
#define TN_PERF_PAPI_RECORD()
#endif
