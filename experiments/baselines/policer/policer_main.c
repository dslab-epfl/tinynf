// changed from original policer:
// - manually get the IPv4 header instead of using nf-util.h which relies on Vigor's packet-io which has global variables
// - add includes that were necessary but for which Vigor relies on brittle compilation order

#include <errno.h>
#include <stdio.h>
#include <stdint.h>
#include <string.h>

#include "nf.h"
#include "nf-log.h"
#include "policer_config.h"
#include "state.h"
#include "dynamic_value.h"
#include "dynamic_value.h.gen.h"
#include "ip_addr.h"

#include "libvig/verified/double-chain.h"
#include "libvig/verified/map.h"
#include "libvig/verified/vector.h"
#include "libvig/verified/expirator.h"

#include <rte_ethdev.h>
#include <rte_ether.h>
#include <rte_ip.h>

struct nf_config config;

struct State *dynamic_ft;

int policer_expire_entries(vigor_time_t time) {
  vigor_time_t exp_time =
      VIGOR_TIME_SECONDS_MULTIPLIER * config.burst / config.rate;
  uint64_t time_u = (uint64_t)time;
  // OK because time >= config.burst / config.rate >= 0
  vigor_time_t min_time = time_u - exp_time;

  return expire_items_single_map(dynamic_ft->dyn_heap, dynamic_ft->dyn_keys,
                                 dynamic_ft->dyn_map, min_time);
}

bool policer_check_tb(uint32_t dst, uint16_t size, vigor_time_t time) {
  int index = -1;
  int present = map_get(dynamic_ft->dyn_map, &dst, &index);
  if (present) {
    dchain_rejuvenate_index(dynamic_ft->dyn_heap, index, time);

    struct DynamicValue *value = 0;
    vector_borrow(dynamic_ft->dyn_vals, index, (void **)&value);

    uint64_t time_u = (uint64_t)time;
    uint64_t time_diff = time_u - value->bucket_time;
    if (time_diff <
        config.burst * VIGOR_TIME_SECONDS_MULTIPLIER / config.rate) {
      uint64_t added_tokens =
          time_diff * config.rate / VIGOR_TIME_SECONDS_MULTIPLIER;
      value->bucket_size += added_tokens;
      if (value->bucket_size > config.burst) {
        value->bucket_size = config.burst;
      }
    } else {
      value->bucket_size = config.burst;
    }
    value->bucket_time = time_u;

    bool fwd = false;
    if (value->bucket_size > size) {
      value->bucket_size -= size;
      fwd = true;
    }

    vector_return(dynamic_ft->dyn_vals, index, value);

    return fwd;
  } else {
    if (size > config.burst) {
      NF_DEBUG("  Unknown flow with packet larger than burst size. Dropping.");
      return false;
    }

    int allocated =
        dchain_allocate_new_index(dynamic_ft->dyn_heap, &index, time);
    if (!allocated) {
      NF_DEBUG("No more space in the policer table");
      return false;
    }
    uint32_t *key;
    struct DynamicValue *value = 0;
    vector_borrow(dynamic_ft->dyn_keys, index, (void **)&key);
    vector_borrow(dynamic_ft->dyn_vals, index, (void **)&value);
    *key = dst;
    value->bucket_size = config.burst - size;
    value->bucket_time = time;
    map_put(dynamic_ft->dyn_map, key, index);
    // the other half of the key is in the map
    vector_return(dynamic_ft->dyn_keys, index, key);
    vector_return(dynamic_ft->dyn_vals, index, value);

    NF_DEBUG("  New flow. Forwarding.");
    return true;
  }
}

bool nf_init() {
  unsigned capacity = config.dyn_capacity;
  dynamic_ft = alloc_state(capacity, rte_eth_dev_count());
  return dynamic_ft != NULL;
}

int nf_process(uint16_t device, uint8_t* buffer, uint16_t buffer_length, vigor_time_t now) {
  NF_DEBUG("Received packet");
  struct ether_hdr *ether_header = (struct ether_hdr*) buffer;
  struct ipv4_hdr *ipv4_header = ether_header->ether_type == 0x8 ? ((struct ipv4_hdr*) buffer + sizeof(struct ether_hdr)) : NULL;
  if (ipv4_header == NULL) {
    NF_DEBUG("Not IPv4, dropping");
    return device;
  }

  policer_expire_entries(now);

  if (device == config.lan_device) {
    // Simply forward outgoing packets.
    NF_DEBUG("Outgoing packet. Not policing.");
    return config.wan_device;
  } else if (device == config.wan_device) {
    // Police incoming packets.
    bool fwd = policer_check_tb(ipv4_header->dst_addr, buffer_length, now);

    if (fwd) {
      NF_DEBUG("Incoming packet within policed rate. Forwarding.");
      return config.lan_device;
    } else {
      NF_DEBUG("Incoming packet outside of policed rate. Dropping.");
      return config.wan_device;
    }
  } else {
     // Drop any other packets.
     NF_DEBUG("Unknown port. Dropping.");
     return device;
  }
}
