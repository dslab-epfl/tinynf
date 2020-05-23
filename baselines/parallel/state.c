#include "state.h"
#include <stdlib.h>
#include "libvig/verified/boilerplate-util.h"
#include "flow.h"
#include "flow.h.gen.h"
struct State* allocated_nf_state = NULL;
struct State* alloc_state(int max_flows, int start_port, uint32_t ext_ip, uint32_t nat_device)
{
  if (allocated_nf_state != NULL) return allocated_nf_state;
  struct State* ret = malloc(sizeof(struct State));
  if (ret == NULL) return NULL;
  ret->fm = NULL;
  if (map_allocate(FlowId_eq, FlowId_hash, max_flows, &(ret->fm)) == 0) return NULL;
  ret->fv = NULL;
  if (vector_allocate(sizeof(struct FlowId), max_flows, FlowId_allocate, &(ret->fv)) == 0) return NULL;
  ret->heap = NULL;
  if (dchain_allocate(max_flows, &(ret->heap)) == 0) return NULL;
  ret->max_flows = max_flows;
  ret->start_port = start_port;
  ret->ext_ip = ext_ip;
  ret->nat_device = nat_device;
  allocated_nf_state = ret;
  return ret;
}
