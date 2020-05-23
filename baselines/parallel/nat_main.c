#include <stdlib.h>

#include "nf.h"
#include "flow.h.gen.h"
#include "nat_flowmanager.h"
#include "nat_config.h"
#include "nf-util.h"

struct nf_config config;

struct FlowManager* flow_manager;


static uint64_t locks[2];

#define LOCK(d) while(!__sync_lock_test_and_set(&locks[(d)], 1)) while(locks[(d)]) __builtin_ia32_pause();
#define UNLOCK(d) __sync_lock_release(&locks[(d)]);

bool nf_init(void) {
  locks[0] = 0;
  locks[1] = 0;

  flow_manager = flow_manager_allocate(
      config.start_port, config.external_addr, config.wan_device,
      config.expiration_time, config.max_flows);

  return flow_manager != NULL;
}

int nf_process(uint16_t device, uint8_t* buffer, uint16_t buffer_length, vigor_time_t now) {
  LOCK(device);

  if (device == 0) {
    LOCK(1-device);
    flow_manager_expire(flow_manager, now);
    UNLOCK(1-device);
  }

  struct ether_hdr *ether_header = nf_then_get_ether_header(buffer);
  uint8_t *ip_options;
  struct ipv4_hdr *ipv4_header =
      nf_then_get_ipv4_header(ether_header, buffer, &ip_options);
  if (ipv4_header == NULL) {
    UNLOCK(device);
    return device;
  }
  struct tcpudp_hdr *tcpudp_header =
      nf_then_get_tcpudp_header(ipv4_header, buffer);
  if (tcpudp_header == NULL) {
    UNLOCK(device);
    return device;
  }

  uint16_t dst_device;
  if (device == config.wan_device) {

    struct FlowId internal_flow;
    if (flow_manager_get_external(flow_manager, tcpudp_header->dst_port, now,
                                  &internal_flow)) {
      if (internal_flow.dst_ip != ipv4_header->src_addr |
          internal_flow.dst_port != tcpudp_header->src_port |
          internal_flow.protocol != ipv4_header->next_proto_id) {
        UNLOCK(device);
        return device;
      }

      ipv4_header->dst_addr = internal_flow.src_ip;
      tcpudp_header->dst_port = internal_flow.src_port;
      dst_device = internal_flow.internal_device;
    } else {
      UNLOCK(device);
      return device;
    }
  } else {
    struct FlowId id = { .src_port = tcpudp_header->src_port,
                         .dst_port = tcpudp_header->dst_port,
                         .src_ip = ipv4_header->src_addr,
                         .dst_ip = ipv4_header->dst_addr,
                         .protocol = ipv4_header->next_proto_id,
                         .internal_device = device };
    uint16_t external_port;
    if (!flow_manager_get_internal(flow_manager, &id, now, &external_port)) {
      LOCK(1-device);
      bool allocate_result = flow_manager_allocate_flow(flow_manager, &id, device, now, &external_port);
      UNLOCK(1-device);
      if (!allocate_result) {
        UNLOCK(device);
        return device;
      }
    }
    ipv4_header->src_addr = config.external_addr;
    tcpudp_header->src_port = external_port;
    dst_device = config.wan_device;
  }

  nf_set_ipv4_udptcp_checksum(ipv4_header, tcpudp_header, buffer);
  ether_header->s_addr = config.device_macs[dst_device];
  ether_header->d_addr = config.endpoint_macs[dst_device];

  UNLOCK(device);
  return dst_device;
}
