// Time abstraction

#pragma once

#include <stdint.h>


// Sleeps for at least the given amount of microseconds.
// It is acceptable but inefficient to sleep for more than that.
void tn_sleep_us(uint64_t microseconds);
