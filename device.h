#include <stdint.h>


void tn_dev_init(void);

void tn_dev_receive(void);

void tn_dev_transmit(void);

// TODO: tn_dev_drop(void);

void* tn_dev_get_packet(void);
int16_t tn_dev_get_packet_length(void);
