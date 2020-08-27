#pragma once

#include <cmdline_parse.h>

#include <inttypes.h>
#include <netinet/in.h>
#include <stdio.h>


#define CMDLINE_IPADDR_V4 42

struct cmdline_token_ipaddr_data
{
	uint8_t flags;
};

struct cmdline_token_ipaddr
{
	struct cmdline_token_ipaddr_data ipaddr_data;
};

typedef struct cmdline_token_ipaddr cmdline_parse_token_ipaddr_t;

struct cmdline_ipaddr {
	union {
		struct in_addr ipv4;
	} addr;
};

static inline int cmdline_parse_ipaddr(cmdline_parse_token_hdr_t* tk, const char* srcbuf, void* res, unsigned ressize)
{
	uint8_t* out = (uint8_t*) res;
	sscanf(srcbuf, "%"SCNu8".%"SCNu8".%"SCNu8".%"SCNu8, out, out+1, out+2, out+3);
	return 0;
}
