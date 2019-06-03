#pragma once

#include <stdint.h>


int tn_dev_init(void);

void tn_dev_receive(void);

void tn_dev_transmit(void);

// TODO: tn_dev_drop(void);

uintptr_t tn_dev_get_packet(void);
uint16_t tn_dev_get_packet_length(void);
