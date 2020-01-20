#pragma once

#include <inttypes.h>
#include <stdio.h>
#include <x86intrin.h>

#include "papi.h"


struct perf_measurement {
	uint64_t tsc;
	const char* name;
};

static uint64_t perf_index;
static struct perf_measurement perf_measurements[10 * 1024 * 1024];

// Cycle-counting functions: call START, then RECORD("event name"), and DUMP at the end
#define TN_PERF_CYCLES_RECORD(text) do { _mm_mfence(); _mm_lfence(); perf_measurements[perf_index].tsc = __rdtsc(); perf_measurements[perf_index].name = text; perf_index++; _mm_lfence(); } while(0)
#define TN_PERF_CYCLES_START() do { perf_index = 0; TN_PERF_RECORD("init"); } while(0)
#define TN_PERF_CYCLES_DUMP() do { for (uint64_t n = 1; n < perf_index; n++) { printf("%s: %"PRIu64"\n", perf_measurements[n].name, perf_measurements[n].tsc - perf_measurements[n-1].tsc); } fflush(stdout); } while(0)


static int papi_events[] = {PAPI_TOT_CYC, PAPI_TOT_INS, PAPI_L1_DCM, PAPI_L1_ICM, PAPI_L2_TCM, PAPI_L3_TCM};
static uint64_t papi_counter;
#define papi_events_count sizeof(papi_events)/sizeof(papi_events[0])
#define TN_PERF_PAPI_BATCH_SIZE 10000
static long long papi_values[TN_PERF_PAPI_BATCH_SIZE][papi_events_count]; \

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
			papi_counter = 0; \
			for (uint64_t n = 0; n < TN_PERF_PAPI_BATCH_SIZE; n++) { \
				for (uint64_t e = 0; e < papi_events_count; e++) { \
					printf("%lld ", papi_values[n][e]); \
				} \
				printf("\n"); \
			} \
		} \
	} while(0)
