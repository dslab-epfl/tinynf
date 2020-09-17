// Performance measurement utility, with three functions:
// - TN_PERF_INIT(), to call at the beginning
// - TN_PERF_RESET(), to call before the measured event(s)
// - TN_PERF_RECORD(batch_size), to call after the measured event(s), with batch_size indicating the number of events
// Once TN_DEBUG_PERF events have been recorded (plus some for heatup), all counters are printed to standard out and the program exits. Remaining events in a batch are discarded.
// To enable this utility, define TN_DEBUG_PERF and link with libPAPI, patched to remove the line 'LIBCFLAGS += -fvisibility=hidden' from src/Rules.pfm4_pe, to allow linking with private functions

// DISCLAIMER:
// This utility attempts to measure the overhead of the measurements themselves and to remove it from the resulting values.
// As part of this, instead of calling PAPI methods directly, it calls internal methods, to avoid the per-call overhead of looking up event sets and such.
// This removes most of the nondeterminism from normal PAPI calls, but it is not possible to reduce the overhead to zero;
// furthermore, by definition, measurement overheads are not independent of measurements, because the measurement code also uses the CPU cache and other internals.
// Thus, while this code does its best to make overheads deterministic, the resulting values should not be taken as objectively 100% correct.
// In fact, some individual data points may make little sense: given minimum overhead MIN and average overhead AVG, if a data point is < (AVG-MIN),
// and the overhead for that data point happens to be MIN, then the resulting data point will be negative! But on average things should be okay.
// Another issue is that of cycles: because measuring cycles requires a serializing instruction to ensure the result makes sense on an out-of-order CPU,
// the number of cycles is artificially lower when using large batches, since only one such instruction is used per batch and the CPU can reorder instructions within a batch,
// even though the CPU would also reorder instructions across batches without this measurement code.
// Thus, while the measured instruction and cache hit counts are accurate, the measured cycle counts should be taken with a pinch of salt.

// Implementation notes:
// There are a few things one can configure, see "Configuration" below.
// This file uses macros to implement "functions" that _must_ be inlined because they are on a hot path.

#pragma once

#ifdef TN_DEBUG_PERF
#include <stddef.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

// Standard PAPI include
#include "papi.h"

// Not so standard PAPI include; expects OSCONTEXT and OSLOCK to contain the name of headers. We only care about Linux anyway...
// And we need papi_vector.h for _papi_hwd
// Also, it triggers a GCC warning so let's ignore that
#define OSCONTEXT "linux-context.h"
#define OSLOCK "linux-lock.h"
#pragma GCC diagnostic push
#pragma GCC diagnostic ignored "-Wvariadic-macros"
#include "papi_internal.h"
#include "papi_vector.h"
#pragma GCC diagnostic pop



// --- Configuration ---

// Which events to measure.
//   PAPI can't measure L1d hits directly on our machine so we have to compute it from memory insructions and L1d misses
static int papi_events[] = {PAPI_REF_CYC, PAPI_TOT_INS, PAPI_LD_INS, PAPI_SR_INS, PAPI_L1_DCM, PAPI_L2_TCM};
#define papi_events_count sizeof(papi_events)/sizeof(papi_events[0])
// How many iterations to (1) throw away at the start, (2) measure after that to quantify per-measurement overhead, and (3) throw away at the start of 'real' measurements
#define papi_heatup_count 100000



// --- Custom PAPI functions ---

// The reason we need these is to make the measurement overhead both lower and more deterministic.
// Measuring the overhead and subtracting it from further measurements is only feasible if it's deterministic,
// and this is not the case if e.g. PAPI is constantly looking up the context associated with our event set, which also pollutes the cache
// Remember, we are measuring packet-processing functions, in which a few dozen cycles is a big deal!
// With these functions, the overhead is much closer to a constant than when calling PAPI directly

static int papi_event_set = PAPI_NULL;
static hwd_context_t* papi_context;
static int (*papi_read)(hwd_context_t*, hwd_control_state_t*, long long**, int);
static int (*papi_reset)(hwd_context_t*, hwd_control_state_t*);
static int papi_state;
static hwd_control_state_t* papi_ctl_state;

static inline void custompapi_init(void) {
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
	if ((papi_ret = PAPI_add_events(papi_event_set, papi_events, papi_events_count)) != PAPI_OK) {
		printf("Couldn't add events to the PAPI event set! Error: %s\n", PAPI_strerror(papi_ret));
		exit(1);
	}
	if ((papi_ret = PAPI_start(papi_event_set)) != PAPI_OK) {
		printf("Couldn't start PAPI! Error: %s\n", PAPI_strerror(papi_ret));
		exit(1);
	}
	// Inlined from PAPI_read
	EventSetInfo_t* papi_ESI = _papi_hwi_lookup_EventSet(papi_event_set);
	if (papi_ESI == NULL || _papi_hwi_invalid_cmp(papi_ESI->CmpIdx) < 0) {
		printf("Bad PAPI ESI...\n");
		exit(1);
	}
	if (_papi_hwi_is_sw_multiplex(papi_ESI)) {
		printf("PAPI multiplex stuff? Not sure what to do with that, sorry...\n");
		exit(1);
	}
	papi_context = _papi_hwi_get_context(papi_ESI, NULL);
	papi_read = _papi_hwd[papi_ESI->CmpIdx]->read;
	papi_reset = _papi_hwd[papi_ESI->CmpIdx]->reset;
	papi_state = papi_ESI->state;
	papi_ctl_state = papi_ESI->ctl_state;
	for (size_t e = 0; e < papi_events_count; e++) {
		if (e != (size_t) papi_ESI->EventInfoArray[e].pos[0]) {
			printf("PAPI index mismatch, sorry, that's not handled...\n");
			exit(1);
		}
	}
}

// Inlined from PAPI_reset
#define custompapi_reset() papi_reset(papi_context, papi_ctl_state)

// Inlined from _papi_hwi_read, itself inlined from PAPI_read; plus a serializing instruction
static long long* papi_dp;
#define custompapi_read(values) do { \
	__asm__ volatile("CPUID" ::: "eax", "ebx", "ecx", "edx", "memory"); \
	papi_read(papi_context, papi_ctl_state, &papi_dp, papi_state); \
	memcpy(values, papi_dp, papi_events_count * sizeof(long long)); \
} while (0)



// --- Measurement ---

static size_t papi_counter;
static uint8_t papi_batches[TN_DEBUG_PERF+papi_heatup_count];
static long long papi_discard_values[papi_events_count];
static long long papi_heatup_values[papi_heatup_count][papi_events_count];
static double papi_heatup_averages[papi_events_count];
static long long papi_values[TN_DEBUG_PERF+papi_heatup_count][papi_events_count];

static inline void TN_PERF_PAPI_INIT(void) {
	custompapi_init();
	// Throwaway heatup first
	for (size_t n = 0; n < papi_heatup_count; n++) {
		custompapi_reset();
		custompapi_read(papi_discard_values);
	}
	// Real heatup next
	for (size_t n = 0; n < papi_heatup_count; n++) {
		custompapi_reset();
		custompapi_read(papi_heatup_values[n]);
	}
	// Then average that to get the baseline level.
	// Averaging isn't great since it doesn't capture the exact PAPI overhead, but it's good enough... not much else we can do.
	for (size_t e = 0; e < papi_events_count; e++) {
		for (size_t n = 0; n < papi_heatup_count; n++) {
			papi_heatup_averages[e] += papi_heatup_values[n][e];
		}
		papi_heatup_averages[e] /= papi_heatup_count;
	}
}
static inline void TN_PERF_PAPI_END(void) {
	// This method is not intended to be called directly.
	PAPI_stop(papi_event_set, papi_discard_values);
	printf("Counters: cycles, instructions, L1d hits, L2 hits, L3/mem hits\n");
	for (size_t n = papi_heatup_count; n < TN_DEBUG_PERF + papi_heatup_count; n++) {
		size_t m;
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
	custompapi_reset(); \
} while(0)
#define TN_PERF_PAPI_RECORD(batch_count) do { \
	custompapi_read(papi_values[papi_counter]); \
	papi_batches[papi_counter] = batch_count; \
	papi_counter += batch_count; \
	if (papi_counter >= TN_DEBUG_PERF + papi_heatup_count) { \
		TN_PERF_PAPI_END(); \
	} \
} while(0)
#else
#define TN_PERF_PAPI_INIT()
#define TN_PERF_PAPI_RESET()
#define TN_PERF_PAPI_RECORD(...)
#endif
