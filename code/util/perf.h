// Performance debugging utilities.
// Only enabled if `TN_DEBUG_PERF` is defined; if so, it acts as the number of packets to record before shutting down.
// If enabled, link with libPAPI: https://icl.utk.edu/papi/

#pragma once

#ifdef TN_DEBUG_PERF
#include "papi.h"
#include <stdio.h>
#include <stdlib.h>

// PAPI can't measure L1d hits directly on our machine so we have to compute it from memory insructions and L1d misses
static int papi_events[] = {PAPI_REF_CYC, PAPI_TOT_INS, PAPI_LD_INS, PAPI_SR_INS, PAPI_L1_DCM, PAPI_L2_TCM};
#define papi_heatup_count 100000
#define papi_events_count sizeof(papi_events)/sizeof(papi_events[0])

static int papi_event_set = PAPI_NULL;
static uint64_t papi_counter;
static uint8_t papi_batches[TN_DEBUG_PERF+papi_heatup_count];
static long long papi_heatup_values[papi_heatup_count][papi_events_count];
static double papi_heatup_averages[papi_events_count];
static long long papi_values[TN_DEBUG_PERF+papi_heatup_count][papi_events_count];

// PAPI functions: call START(), then RESET() before your code and RECORD(batch_size) immediately afterwards.
// RECORD will print data and terminate the program when TN_DEBUG_PERF samples have been collected; any remaining samples from that batch are discarded.
// (RESET and RECORD are implemented as macros to guarantee they are inlined)
static inline void TN_PERF_PAPI_START(void) {
	int papi_ret;
	if ((papi_ret = PAPI_library_init(PAPI_VER_CURRENT)) != PAPI_VER_CURRENT) {
		if (papi_ret > 0) {
			printf("PAPI is not the version we expect!");
		} else {
			printf("Couldn't initialize PAPI! Error: %s\n", PAPI_strerror(papi_ret));
		}
		exit(1);
	}
	if ((papi_ret = PAPI_create_eventset(&papi_event_set)) != PAPI_OK) {
		printf("Couldn't create a PAPI event set! Error: %s\n", PAPI_strerror(papi_ret));
		exit(1);
	}
	for (uint64_t e = 0; e < papi_events_count; e++) {
		if ((papi_ret = PAPI_add_event(papi_event_set, papi_events[e])) != PAPI_OK) {
			printf("Couldn't add an event to the PAPI event set! Error: %s\n", PAPI_strerror(papi_ret));
			exit(1);
		}
	}
	if ((papi_ret = PAPI_start(papi_event_set)) != PAPI_OK) {
		printf("Couldn't start PAPI! Error: %s\n", PAPI_strerror(papi_ret));
		exit(1);
	}
	// Run heatup iterations first
	for (uint64_t n = 0; n < papi_heatup_count; n++) {
		PAPI_read(papi_event_set, papi_heatup_values[0]);
		PAPI_reset(papi_event_set);
	}
	// Then real iterations
	for (uint64_t n = 0; n < papi_heatup_count; n++) {
		PAPI_read(papi_event_set, papi_heatup_values[n]);
		PAPI_reset(papi_event_set);
	}
	// Then average that to get the baseline level.
	// Averaging isn't great since it doesn't capture the exact PAPI overhead, but it's good enough... not much else we can do.
	for (uint64_t e = 0; e < papi_events_count; e++) {
		for (uint64_t n = 0; n < papi_heatup_count; n++) {
			papi_heatup_averages[e] += papi_heatup_values[n][e];
		}
		papi_heatup_averages[e] /= papi_heatup_count;
		printf("PAPI HEATUP: %lf\n", papi_heatup_averages[e]);
	}
}
static inline void TN_PERF_PAPI_END(void) {
	// This method is not intended to be called directly.
	printf("Counters: cycles, instructions, L1d hits, L2 hits, L3/mem hits\n");
	for (uint64_t n = papi_heatup_count; n < TN_DEBUG_PERF + papi_heatup_count; n++) {
		uint64_t m;
		for (m = 0; m < papi_batches[n] && n + m < TN_DEBUG_PERF + papi_heatup_count; m++) {
			printf("%lf %lf %lf %lf %lf\n",
				((double) papi_values[n][0] - papi_heatup_averages[0]) / papi_batches[n],
				((double) papi_values[n][1] - papi_heatup_averages[1]) / papi_batches[n],
				(((double) papi_values[n][2] - papi_heatup_averages[2]) + ((double) papi_values[n][3] - papi_heatup_averages[3]) - ((double) papi_values[n][4] - papi_heatup_averages[4])) / papi_batches[n],
				(((double) papi_values[n][4] - papi_heatup_averages[4]) - ((double) papi_values[n][5] - papi_heatup_averages[5])) / papi_batches[n],
				((double) papi_values[n][5] - papi_heatup_averages[5]) / papi_batches[n]
			);
		}
		n += m - 1;
	}
	exit(0);
}
#define TN_PERF_PAPI_RESET() do { \
	PAPI_read(papi_event_set, papi_values[papi_counter]); \
	PAPI_reset(papi_event_set); \
} while(0)
#define TN_PERF_PAPI_RECORD(batch_count) do { \
	PAPI_read(papi_event_set, papi_values[papi_counter]); \
	papi_batches[papi_counter] = batch_count; \
	papi_counter += batch_count; \
	if (papi_counter >= TN_DEBUG_PERF + papi_heatup_count) { \
		TN_PERF_PAPI_END(); \
	} \
} while(0)
#else
#define TN_PERF_PAPI_START()
#define TN_PERF_PAPI_RESET()
#define TN_PERF_PAPI_RECORD(...)
#endif
