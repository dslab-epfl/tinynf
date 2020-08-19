#pragma once

#include <stdbool.h>
#include <stdint.h>

#include "libvig/verified/vigor-time.h"

#define FLOOD_FRAME ((uint16_t) -1)

struct nf_config;

bool nf_init(uint16_t nb_devices);
int nf_process(uint16_t device, uint8_t* buffer, uint16_t packet_length, vigor_time_t now);

extern struct nf_config config;
void nf_config_init(uint16_t nb_devices, int argc, char **argv);
void nf_config_usage(void);
void nf_config_print(void);

#ifdef KLEE_VERIFICATION
void nf_loop_iteration_border(unsigned lcore_id, vigor_time_t time);
#endif
