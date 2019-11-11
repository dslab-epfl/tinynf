#pragma once

int rte_errno;

static inline const char* rte_strerror(int errnum)
{
	(void) errnum;

	return "Sorry, this is a stub, no idea what the error is.";
}
