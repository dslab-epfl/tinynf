#ifndef _FLOWMANAGER_H_INCLUDED_
#define _FLOWMANAGER_H_INCLUDED_

#include "flow.h.gen.h"
#include "libvig/verified/vigor-time.h"

#include <stdbool.h>
#include <stdint.h>

struct FlowManager;

struct FlowManager *
flow_manager_allocate(uint16_t starting_port, uint32_t nat_ip,
                      uint16_t nat_device, /* NOTE: only required for verif to
                                              show that internal != external;
                                              can be removed once "our NAT" ==
                                              router + "only NAT" */
                      uint32_t expiration_time, uint64_t max_flows);

bool flow_manager_allocate_flow(struct FlowManager *manager, struct FlowId *id,
                                uint16_t internal_device, vigor_time_t time,
                                uint16_t *external_port);
void flow_manager_expire(struct FlowManager *manager, vigor_time_t time);
bool flow_manager_get_internal(struct FlowManager *manager, struct FlowId *id,
                               vigor_time_t time, uint16_t *external_port);
bool flow_manager_get_external(struct FlowManager *manager,
                               uint16_t external_port, vigor_time_t time,
                               struct FlowId *out_flow);
#endif //_FLOWMANAGER_H_INCLUDED_
