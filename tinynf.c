#include <stdbool.h>
#include <stdint.h>

// needs to be a multiple of 128; being 128 allows us to use a single hugepage for all buffers
#define NIC_QUEUE_LENGTH 128


// Receive state
uint64_t recv_base;
uint64_t recv_head;
uint64_t recv_tail;


// Send state
uint64_t send_base;
uint64_t send_head;
uint64_t send_tail;


// Packet processing state
void* tn_packet;
uint16_t tn_packet_length;

// Initialization; returns 0 or an error code
int tn_init()
{
	// Allocate 1 hugepage (enough for 128 16KB packet buffers)
	// Detect the NICs
	// read the 1st memory line in /resource; then any reg is just the memory addr + reg
	// Initialize the NICs
	// Create 1 RX, 1 TX queue on NICs
	// Start the NICs
	// Set NICs to promiscuous mode (or do that before start?)
	// Our custom setup:
	// - All RX_DD = 0
	// - RX_HD/TL = 0
	// - All TX_DD = 1
	// - TX_HD/TL = 0
	// - RX[n] = TX[n] = &hugepage[n * 16 * 1024]
}


// Receive and send
void tn_recv()
{
}

void tn_drop()
{
	// TODO how?
	// can we "send" a packet but with zero bytes or something?
}

void tn_send()
{
}


// Packet processing
int main()
{
	int init_ret = nf_init();
	if (init_ret != 0) {
		return init_ret;
	}

	while(true) {
		tn_recv();
		tn_send(); // or tn_drop();
	}
}
