#include "ip_addr.h.gen.h"

#include <stdint.h>

bool ip_addr_eq(void* a, void* b)
//@ requires [?f1]ip_addrp(a, ?aid) &*& [?f2]ip_addrp(b, ?bid);
/*@ ensures [f1]ip_addrp(a, aid) &*& [f2]ip_addrp(b, bid) &*&
            (result ? aid == bid : aid != bid); @*/
{
  struct ip_addr* id1 = (struct ip_addr*) a;
  struct ip_addr* id2 = (struct ip_addr*) b;
  //@ open [f1]ip_addrp(a, aid);
  //@ open [f2]ip_addrp(b, bid);
  return (id1->addr == id2->addr);
  //@ close [f1]ip_addrp(a, aid);
  //@ close [f2]ip_addrp(b, bid);

}


void ip_addr_allocate(void* obj)
//@ requires chars(obj, sizeof(struct ip_addr), _);
//@ ensures ip_addrp(obj, DEFAULT_IP_ADDR);
{
  //@ close_struct((struct ip_addr*) obj);
  struct ip_addr* id = (struct ip_addr*) obj;
  id->addr = 0;
  //@ close ip_addrp(obj, DEFAULT_IP_ADDR);
}


#ifdef KLEE_VERIFICATION
struct str_field_descr ip_addr_descrs[] = {
  {offsetof(struct ip_addr, addr), sizeof(uint32_t ), 0, "addr"},
};
struct nested_field_descr ip_addr_nests[] = {

};
unsigned ip_addr_hash(void* obj)
{
  klee_trace_ret();
  klee_trace_param_tagged_ptr(obj, sizeof(struct ip_addr),
                             "obj", "ip_addr", TD_BOTH);
  for (int i = 0; i < sizeof(ip_addr_descrs)/sizeof(ip_addr_descrs[0]); ++i) {
    klee_trace_param_ptr_field_arr_directed(obj,
                                            ip_addr_descrs[i].offset,
                                            ip_addr_descrs[i].width,
                                            ip_addr_descrs[i].count,
                                            ip_addr_descrs[i].name,
                                            TD_BOTH);
  }  for (int i = 0; i < sizeof(ip_addr_nests)/sizeof(ip_addr_nests[0]); ++i) {
    klee_trace_param_ptr_nested_field_arr_directed(obj,
                                                  ip_addr_nests[i].base_offset,
                                                  ip_addr_nests[i].offset,
                                                  ip_addr_nests[i].width,
                                                  ip_addr_nests[i].count,
                                                  ip_addr_nests[i].name,
                                                  TD_BOTH);
  }  return klee_int("ip_addr_hash");}

#else//KLEE_VERIFICATION

unsigned ip_addr_hash(void* obj)
//@ requires [?f]ip_addrp(obj, ?v);
//@ ensures [f]ip_addrp(obj, v) &*& result == _ip_addr_hash(v);
{
  struct ip_addr* id = (struct ip_addr*) obj;

  //@ open [f]ip_addrp(obj, v);
  //@ close [f]ip_addrp(obj, v);

  unsigned hash = 0;
  hash = __builtin_ia32_crc32si(hash, id->addr);
  return hash;
}

#endif//KLEE_VERIFICATION

