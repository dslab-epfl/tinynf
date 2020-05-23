#ifndef _STATE_H_INCLUDED_
#define _STATE_H_INCLUDED_
#include <stdint.h>
#include <stdbool.h>
#include "libvig/verified/map.h"
#include "libvig/verified/double-chain.h"
#include "libvig/verified/vector.h"
struct State {
  struct Map* fm;
  struct Vector* fv;
  struct DoubleChain* heap;
  int max_flows;
  int start_port;
  uint32_t ext_ip;
  uint32_t nat_device;
};

struct State* alloc_state(int max_flows, int start_port, uint32_t ext_ip, uint32_t nat_device);
#endif//_STATE_H_INCLUDED_
