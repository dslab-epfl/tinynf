#pragma once

#include <cmdline_parse.h>

#include <inttypes.h>
#include <stdio.h>


static inline int cmdline_parse_etheraddr(cmdline_parse_token_hdr_t* tk, const char* srcbuf, void* res, unsigned ressize)
{
	// No error handling, we assume all is fine
	uint8_t* out = (uint8_t*) res;
	sscanf(srcbuf, "%"SCNx8":%"SCNx8":%"SCNx8":%"SCNx8":%"SCNx8":%"SCNx8, out, out+1, out+2, out+3, out+4, out+5);
	return 0;
}
