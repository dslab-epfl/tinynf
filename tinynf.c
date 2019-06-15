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
	uint8_t* packet = (uint8_t*) tn_dev_get_packet();
//	uint16_t packet_len = tn_dev_get_packet_length();
//	for (uint16_t n = 0; n < packet_len; n++) {
//		printf("0x%02"PRIx8" ", packet[n]);
//	}
	// SRC MAC (90:e2:ba:55:14:11)
	packet[0] = 0x90;
	packet[1] = 0xE2;
	packet[2] = 0xBA;
	packet[3] = 0x55;
	packet[4] = 0x14;
	packet[5] = 0x11;
	// DST MAC (01:02:03:04:05:06)
	packet[6] = 0x01;
	packet[7] = 0x02;
	packet[8] = 0x03;
	packet[9] = 0x04;
	packet[10]= 0x05;
	packet[11]= 0x06;

//	tn_dev_send();
printf("Sent a packet!\n");

	return 0;
}
