#include "device.h"

#include <stdio.h>
#include <inttypes.h>

// Packet processing
int main()
{
	int ret = tn_dev_init();
	if (ret != 0) {
		return ret;
	}
printf("Initialized successfully!\n");
	tn_dev_receive();
printf("Received a packet!\n");
	uint16_t packet_len = tn_dev_get_packet_length();
	uint8_t* packet = (uint8_t*) tn_dev_get_packet();
	for (int n = 0; n < packet_len; n++) {
		printf("%"PRIx8" ", packet[n]);
	}
	return 0;
}
