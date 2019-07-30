#pragma once

#include <inttypes.h>
#include <stdio.h>
#include <x86intrin.h>


struct perf_measurement {
	uint64_t tsc;
	const char* name;
};

uint64_t perf_index;
struct perf_measurement perf_measurements[10 * 1024 * 1024];

#define TN_PERF_RECORD(text) _mm_mfence(); _mm_lfence(); perf_measurements[perf_index].tsc = __rdtsc(); perf_measurements[perf_index].name = text; perf_index++; _mm_lfence();

#define TN_PERF_START() perf_index = 0; TN_PERF_RECORD("init");

#define TN_PERF_DUMP() for (uint64_t n = 1; n < perf_index; n++) { printf("%s: %"PRIu64"\n", perf_measurements[n].name, perf_measurements[n].tsc - perf_measurements[n-1].tsc); } fflush(stdout);
