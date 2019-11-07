#include "../time.h"

#include <assert.h>
#include <errno.h>
#include <stdbool.h>
#include <stdint.h>
#include <time.h>

void tn_sleep_us(uint64_t microseconds)
{
	struct timespec request;
	request.tv_sec = (int64_t)(microseconds / 1000000);
	request.tv_nsec = (int64_t)(microseconds % 1000000) * 1000;

	// TODO if the kernel misbehaves we'll halt forever, not nice, we should crash instead with some kind of retry limit
	while (true) {
		// Note that usleep was removed in POSIX-2008
		// Also, we don't care if we end up sleeping more than requested due to interrupts and restarts.
		// (properly doing it with clock_gettime then clock_nanosleep in absolute time would require handling time overflows; not fun)
		struct timespec remain;
		int ret = nanosleep(&request, &remain);
		if (ret == 0) {
			return;
		}
		if (ret == EINTR) {
			// Got interrupted; try again.
			request.tv_sec = remain.tv_sec;
			request.tv_nsec = remain.tv_nsec;
			continue;
		}
		// Other codes cannot happen according to the documentation.
		assert(0);
	}
}
