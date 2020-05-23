#ifndef _ip_addr_GEN_H_INCLUDED_
#define _ip_addr_GEN_H_INCLUDED_

#include <stdbool.h>
#include "libvig/verified/boilerplate-util.h"

#include "libvig/verified/ether.h"


#include "ip_addr.h"

#define DEFAULT_IP_ADDR ip_addrc(0)

/*@
inductive ip_addri = ip_addrc(uint32_t ); @*/

/*@
predicate ip_addrp(struct ip_addr* ptr; ip_addri v) = 
  struct_ip_addr_padding(ptr) &*&
  ptr->addr |-> ?addr_f &*&
  v == ip_addrc(addr_f); @*/

/*@
fixpoint unsigned _ip_addr_hash(ip_addri x) {
  switch(x) { case ip_addrc(addr_f):
    return crc32_hash(0, addr_f);
  }
} @*/

unsigned ip_addr_hash(void* obj);
//@ requires [?f]ip_addrp(obj, ?v);
//@ ensures [f]ip_addrp(obj, v) &*& result == _ip_addr_hash(v);

bool ip_addr_eq(void* a, void* b);
//@ requires [?f1]ip_addrp(a, ?aid) &*& [?f2]ip_addrp(b, ?bid);
/*@ ensures [f1]ip_addrp(a, aid) &*& [f2]ip_addrp(b, bid) &*&
            (result ? aid == bid : aid != bid); @*/

void ip_addr_allocate(void* obj);
//@ requires chars(obj, sizeof(struct ip_addr), _);
//@ ensures ip_addrp(obj, DEFAULT_IP_ADDR);

#define LOG_IP_ADDR(obj, p); \
  p("{"); \
  p("addr: %d", (obj)->addr); \
  p("}");


#ifdef KLEE_VERIFICATION
#  include <klee/klee.h>
#  include "libvig/models/str-descr.h"

extern struct str_field_descr ip_addr_descrs[1];
extern struct nested_field_descr ip_addr_nests[0];
#endif//KLEE_VERIFICATION

#endif//_ip_addr_GEN_H_INCLUDED_
