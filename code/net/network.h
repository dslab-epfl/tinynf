#pragma once

#include <stdbool.h>
#include <stdint.h>

#include "env/pci.h"


// Configuration API:

struct tn_net_device;
struct tn_net_pipe;

bool tn_net_device_init(struct tn_pci_device pci_device, struct tn_net_device** out_device);
bool tn_net_device_set_promiscuous(const struct tn_net_device* device);

bool tn_net_pipe_init(struct tn_net_pipe** out_pipe);
bool tn_net_pipe_set_receive(struct tn_net_pipe* pipe, const struct tn_net_device* device, uint64_t queue_index);
bool tn_net_pipe_add_send(struct tn_net_pipe* pipe, const struct tn_net_device* device, uint64_t queue_index);


// Low-level processing API:

// Returns true iff there is a packet to process, in which case the out_ arguments point to valid data
bool tn_net_pipe_receive(struct tn_net_pipe* pipe, uint8_t** out_packet, uint16_t* out_packet_length);
// Must be called exactly once after receive
void tn_net_pipe_send(struct tn_net_pipe* pipe, uint16_t packet_length, bool* send_list);


// High-level processing API:

// Returns the new length of the packet, and sets send_list[N] = true iff the packet should be sent on queue N
// (queues are in the order they were added)
typedef uint16_t tn_net_packet_handler(uint8_t* packet, uint16_t packet_length, bool* send_list);
void tn_net_pipe_process(struct tn_net_pipe* pipe, tn_net_packet_handler* handler);
