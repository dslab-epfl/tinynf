// TinyNF
#include "net/network.h"

// Vigor
#include "vigor/nf.h"

#include <stdbool.h>


static uint16_t devices_count;

static uint16_t current_device;
uint16_t compat_packet_handler(uint8_t* packet, uint16_t packet_length, bool* send_list)
{
	vigor_time_t vigor_now = current_time();
	int vigor_output = nf_process(current_device, packet, packet_length, vigor_now);
	if (vigor_output == FLOOD_FRAME) {
		for (uint16_t n = 0; n < devices_count; n++) {
			send_list[n] = true;
		}
	} else if (vigor_output == current_device) {
		// Nothing; this means "drop", Vigor has no notion of sending back to the same device
	} else {
		send_list[vigor_output] = true;
	}
}

int main(int argc, char** argv)
{
	devices_count = argc - 1;

	// TinyNF init
	struct tn_net_pipe* pipes[devices_count];
	???

	// Vigor init
	nf_config_init();
	nf_init();

	// Compat layer
	while(true) {
		for (current_device = 0; current_device < devices_count; current_device++) {
			tn_net_pipe_run_step(pipes[device], compat_packet_handler);
		}
	}
}
