// Network abstractions.
// A 'device' represents a physical network card: https://en.wikipedia.org/wiki/Network_interface_controller
// Devices only handle packets destined to them by default, by looking at packets' MAC address: https://en.wikipedia.org/wiki/MAC_address
// Devices can be set into 'promiscuous' mode to handle all packets regardless of MAC address.
// Each device has one 'queue' to receive packet, and multiple 'queues' to transmit packets.
// An 'agent' handles packets received on one input device, forwarding them through zero or more output devices as needed.

#pragma once

#include <stdbool.h>
#include <stddef.h>
#include <stdint.h>

#include "env/pci.h"


// Configuration API
// -----------------

struct tn_net_device;
struct tn_net_agent;

bool tn_net_device_init(struct tn_pci_address pci_address, struct tn_net_device** out_device);
bool tn_net_device_set_promiscuous(struct tn_net_device* device);

bool tn_net_agent_init(struct tn_net_device* input_device, size_t outputs_count, struct tn_net_device** output_devices, struct tn_net_agent** out_agent);


// Packet processing API
// ---------------------

// Returns the new length of the packet, and sets outputs[N] = whether the packet should be sent on queue N (queues are in the order they were added)
typedef void tn_net_packet_handler(volatile uint8_t* packet, uint16_t packet_length, uint16_t* outputs);
// Runs the agent using the given handlers
void tn_net_run(struct tn_net_agent* agent, tn_net_packet_handler* handler
#ifdef DANGEROUS
, size_t outputs_count
#endif
);
