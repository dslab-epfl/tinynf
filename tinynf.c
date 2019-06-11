#include "device.h"

#include <stdio.h>
#include <inttypes.h>

// Packet processing
int main(int argc, char** argv)
{
	setvbuf(stdout, NULL, _IONBF, 0);

	(void) argc;
	(void) argv;

	int ret = tn_dev_init();
	if (ret != 0) {
		return ret;
	}
printf("Initialized successfully!\n");
	tn_dev_receive();
printf("Received a packet!\n");
	uint16_t packet_len = tn_dev_get_packet_length();
printf("length %"PRIu16"\n",packet_len);
	uint8_t* packet = (uint8_t*) tn_dev_get_packet();
	for (uint16_t n = 0; n < packet_len; n++) {
		printf("0x%02"PRIx8" ", packet[n]);
	}
	return 0;
}
