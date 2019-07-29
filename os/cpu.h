#pragma once

#include <stdbool.h>
#include <stdint.h>


typedef uint32_t node_t;

bool tn_cpu_get_current_node(node_t* out_node);
