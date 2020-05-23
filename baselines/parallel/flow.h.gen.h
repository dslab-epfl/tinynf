#ifndef _FlowId_GEN_H_INCLUDED_
#define _FlowId_GEN_H_INCLUDED_

#include <stdbool.h>
#include "libvig/verified/boilerplate-util.h"

#include "libvig/verified/ether.h"


#include "flow.h"

#define DEFAULT_FLOWID FlowIdc(0, 0, 0, 0, 0, 0)

/*@
inductive FlowIdi = FlowIdc(uint16_t , uint16_t , uint32_t , uint32_t , uint16_t , uint8_t ); @*/

/*@
predicate FlowIdp(struct FlowId* ptr; FlowIdi v) = 
  struct_FlowId_padding(ptr) &*&
  ptr->src_port |-> ?src_port_f &*&
  ptr->dst_port |-> ?dst_port_f &*&
  ptr->src_ip |-> ?src_ip_f &*&
  ptr->dst_ip |-> ?dst_ip_f &*&
  ptr->internal_device |-> ?internal_device_f &*&
  ptr->protocol |-> ?protocol_f &*&
  v == FlowIdc(src_port_f, dst_port_f, src_ip_f, dst_ip_f, internal_device_f, protocol_f); @*/

/*@
fixpoint unsigned _FlowId_hash(FlowIdi x) {
  switch(x) { case FlowIdc(src_port_f, dst_port_f, src_ip_f, dst_ip_f, internal_device_f, protocol_f):
    return crc32_hash(crc32_hash(crc32_hash(crc32_hash(crc32_hash(crc32_hash(0, src_port_f), dst_port_f), src_ip_f), dst_ip_f), internal_device_f), protocol_f);
  }
} @*/

unsigned FlowId_hash(void* obj);
//@ requires [?f]FlowIdp(obj, ?v);
//@ ensures [f]FlowIdp(obj, v) &*& result == _FlowId_hash(v);

bool FlowId_eq(void* a, void* b);
//@ requires [?f1]FlowIdp(a, ?aid) &*& [?f2]FlowIdp(b, ?bid);
/*@ ensures [f1]FlowIdp(a, aid) &*& [f2]FlowIdp(b, bid) &*&
            (result ? aid == bid : aid != bid); @*/

void FlowId_allocate(void* obj);
//@ requires chars(obj, sizeof(struct FlowId), _);
//@ ensures FlowIdp(obj, DEFAULT_FLOWID);

#define LOG_FLOWID(obj, p); \
  p("{"); \
  p("src_port: %d", (obj)->src_port); \
  p("dst_port: %d", (obj)->dst_port); \
  p("src_ip: %d", (obj)->src_ip); \
  p("dst_ip: %d", (obj)->dst_ip); \
  p("internal_device: %d", (obj)->internal_device); \
  p("protocol: %d", (obj)->protocol); \
  p("}");


#ifdef KLEE_VERIFICATION
#  include <klee/klee.h>
#  include "libvig/models/str-descr.h"

extern struct str_field_descr FlowId_descrs[6];
extern struct nested_field_descr FlowId_nests[0];
#endif//KLEE_VERIFICATION

#endif//_FlowId_GEN_H_INCLUDED_
