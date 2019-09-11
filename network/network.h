#pragma once

#include <stdbool.h>
#include <stdint.h>

#include "os/pci.h"


struct tn_net_device;
struct tn_net_pipe;

// Returns the new length of the packet, and sets send_list[N] = true iff the packet should be sent on queue N
// (queues are in the order they were added)
typedef uint16_t tn_net_packet_handler(uint8_t* packet, uint16_t packet_length, bool* send_list);

bool tn_net_device_init(struct tn_pci_device pci_device, struct tn_net_device** out_device);
bool tn_net_device_set_promiscuous(const struct tn_net_device* device);

bool tn_net_pipe_init(struct tn_net_pipe** out_pipe);
bool tn_net_pipe_set_receive(struct tn_net_pipe* pipe, const struct tn_net_device* device, uint64_t queue_index);
bool tn_net_pipe_add_send(struct tn_net_pipe* pipe, const struct tn_net_device* device, uint64_t queue_index);
void tn_net_pipe_run_step(struct tn_net_pipe* pipe, tn_net_packet_handler* handler);
