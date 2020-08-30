// Network abstractions.
// A 'device' represents a physical network card: https://en.wikipedia.org/wiki/Network_interface_controller
// Devices only handle packets destined to them by default, by looking at packets' MAC address: https://en.wikipedia.org/wiki/MAC_address
// Devices can be set into 'promiscuous' mode to handle all packets regardless of MAC address.
// Each device has one 'queue' to receive packet, and multiple 'queues' to transmit packets.
// An 'agent' handles packets received on one input device, forwarding them through zero or more output devices as needed.

#pragma once

#include <stdbool.h>
#include <stdint.h>

#include "env/pci.h"


// Configuration API
// -----------------

struct tn_net_device;
struct tn_net_agent;

bool tn_net_device_init(struct tn_pci_device pci_device, struct tn_net_device** out_device);
bool tn_net_device_set_promiscuous(struct tn_net_device* device);

bool tn_net_agent_init(struct tn_net_agent** out_agent);
bool tn_net_agent_set_input(struct tn_net_agent* agent, struct tn_net_device* device);
bool tn_net_agent_add_output(struct tn_net_agent* agent, struct tn_net_device* device);


// Packet processing API
// ---------------------

// Returns the new length of the packet, and sets outputs[N] = whether the packet should be sent on queue N (queues are in the order they were added)
typedef uint16_t tn_net_packet_handler(uint8_t* packet, uint16_t packet_length, void* state, bool* outputs);
// Runs the agents forever using the given handlers
__attribute__((noreturn))
void tn_net_run(uint64_t agents_count, struct tn_net_agent** agents, tn_net_packet_handler** handlers, void** states);


// Low-level processing API
// ------------------------
// This API only exists for use in compatibility layers, so that programs that use existing C frameworks based on separate receive/transmit can be ported

// Returns true iff there is a packet to process, in which case the out_ arguments point to valid data
bool tn_net_agent_receive(struct tn_net_agent* agent, uint8_t** out_packet, uint16_t* out_packet_length);
// Must be called exactly once after receive (even if the packet is to be dropped by all outputs)
void tn_net_agent_transmit(struct tn_net_agent* agent, uint16_t packet_length, bool* outputs);


