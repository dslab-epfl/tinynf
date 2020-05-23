#include "flow.h.gen.h"

#include <stdint.h>

bool FlowId_eq(void* a, void* b)
//@ requires [?f1]FlowIdp(a, ?aid) &*& [?f2]FlowIdp(b, ?bid);
/*@ ensures [f1]FlowIdp(a, aid) &*& [f2]FlowIdp(b, bid) &*&
            (result ? aid == bid : aid != bid); @*/
{
  struct FlowId* id1 = (struct FlowId*) a;
  struct FlowId* id2 = (struct FlowId*) b;
  //@ open [f1]FlowIdp(a, aid);
  //@ open [f2]FlowIdp(b, bid);
  return (id1->src_port == id2->src_port)
     AND (id1->dst_port == id2->dst_port)
     AND (id1->src_ip == id2->src_ip)
     AND (id1->dst_ip == id2->dst_ip)
     AND (id1->internal_device == id2->internal_device)
     AND (id1->protocol == id2->protocol);
  //@ close [f1]FlowIdp(a, aid);
  //@ close [f2]FlowIdp(b, bid);

}


void FlowId_allocate(void* obj)
//@ requires chars(obj, sizeof(struct FlowId), _);
//@ ensures FlowIdp(obj, DEFAULT_FLOWID);
{
  //@ close_struct((struct FlowId*) obj);
  struct FlowId* id = (struct FlowId*) obj;
  id->src_port = 0;
  id->dst_port = 0;
  id->src_ip = 0;
  id->dst_ip = 0;
  id->internal_device = 0;
  id->protocol = 0;
  //@ close FlowIdp(obj, DEFAULT_FLOWID);
}


#ifdef KLEE_VERIFICATION
struct str_field_descr FlowId_descrs[] = {
  {offsetof(struct FlowId, src_port), sizeof(uint16_t ), 0, "src_port"},
  {offsetof(struct FlowId, dst_port), sizeof(uint16_t ), 0, "dst_port"},
  {offsetof(struct FlowId, src_ip), sizeof(uint32_t ), 0, "src_ip"},
  {offsetof(struct FlowId, dst_ip), sizeof(uint32_t ), 0, "dst_ip"},
  {offsetof(struct FlowId, internal_device), sizeof(uint16_t ), 0, "internal_device"},
  {offsetof(struct FlowId, protocol), sizeof(uint8_t ), 0, "protocol"},
};
struct nested_field_descr FlowId_nests[] = {

};
unsigned FlowId_hash(void* obj)
{
  klee_trace_ret();
  klee_trace_param_tagged_ptr(obj, sizeof(struct FlowId),
                             "obj", "FlowId", TD_BOTH);
  for (int i = 0; i < sizeof(FlowId_descrs)/sizeof(FlowId_descrs[0]); ++i) {
    klee_trace_param_ptr_field_arr_directed(obj,
                                            FlowId_descrs[i].offset,
                                            FlowId_descrs[i].width,
                                            FlowId_descrs[i].count,
                                            FlowId_descrs[i].name,
                                            TD_BOTH);
  }  for (int i = 0; i < sizeof(FlowId_nests)/sizeof(FlowId_nests[0]); ++i) {
    klee_trace_param_ptr_nested_field_arr_directed(obj,
                                                  FlowId_nests[i].base_offset,
                                                  FlowId_nests[i].offset,
                                                  FlowId_nests[i].width,
                                                  FlowId_nests[i].count,
                                                  FlowId_nests[i].name,
                                                  TD_BOTH);
  }  return klee_int("FlowId_hash");}

#else//KLEE_VERIFICATION

unsigned FlowId_hash(void* obj)
//@ requires [?f]FlowIdp(obj, ?v);
//@ ensures [f]FlowIdp(obj, v) &*& result == _FlowId_hash(v);
{
  struct FlowId* id = (struct FlowId*) obj;

  //@ open [f]FlowIdp(obj, v);
  //@ close [f]FlowIdp(obj, v);

  unsigned hash = 0;
  hash = __builtin_ia32_crc32si(hash, id->src_port);
  hash = __builtin_ia32_crc32si(hash, id->dst_port);
  hash = __builtin_ia32_crc32si(hash, id->src_ip);
  hash = __builtin_ia32_crc32si(hash, id->dst_ip);
  hash = __builtin_ia32_crc32si(hash, id->internal_device);
  hash = __builtin_ia32_crc32si(hash, id->protocol);
  return hash;
}

#endif//KLEE_VERIFICATION

