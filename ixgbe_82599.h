#pragma once

#include <stdbool.h>
#include <stdint.h>

// Section 7.2.3.3 Transmit Descriptor Ring:
// "Transmit Descriptor Length register (TDLEN 0-127) — This register determines the number of bytes allocated to the circular buffer. This value must be 0 modulo 128."
// By making this 256, we can use 8-bit unsigned integer as ring indices without extra work
static const uint32_t IXGBE_RING_SIZE = 256;

// Section 8.2.3.8.7 Split Receive Control Registers: "Receive Buffer Size for Packet Buffer. Value can be from 1 KB to 16 KB"
// Section 7.2.3.2.4 Advanced Transmit Data Descriptor: "DTALEN (16): This field holds the length in bytes of data buffer at the address pointed to by this specific descriptor [...]
// Thus we set 8 KB as a power of 2 that can be sent and received.
static const uint32_t IXGBE_PACKET_SIZE_MAX = 8 * 1024;

// This struct is not used in the processing loop.
struct ixgbe_device
{
	uintptr_t addr;
	uint8_t pci_bus;
	uint8_t pci_device;
	uint8_t pci_function;
	uint8_t _padding[5];
};

// This struct is used in the processing loop!
struct ixgbe_queue
{
	uintptr_t device_addr; // TODO consider having the reg address directly, less computation?
	uintptr_t ring_addr;
	uint8_t queue_index;
	uint8_t packet_index; // TODO check if making index/queue uint16 or 32 or 64 makes any difference (changing index will need explicit truncation when it overflows the ring size!)
	uint8_t _padding[6];
};

bool ixgbe_device_get(uint8_t bus, uint8_t device, uint8_t function, struct ixgbe_device* out_device);
bool ixgbe_device_init(const struct ixgbe_device* device);
bool ixgbe_device_set_promiscuous(const struct ixgbe_device* device);

bool ixgbe_device_init_receive_queue(const struct ixgbe_device* device, uint8_t queue_index, uintptr_t buffer_addr, struct ixgbe_queue* out_queue);
bool ixgbe_device_init_send_queue(const struct ixgbe_device* device, uint8_t queue_index, uintptr_t buffer_addr, struct ixgbe_queue* out_queue);

uint16_t ixgbe_receive(struct ixgbe_queue* queue);
void ixgbe_send(struct ixgbe_queue* queue, uint16_t packet_length);

// TODO REMOVE
void ixgbe_sanity_check(uintptr_t addr);
void ixgbe_stats_reset(const uintptr_t addr);
void ixgbe_stats_probe(const uintptr_t addr);
