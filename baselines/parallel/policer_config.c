#include "policer_config.h"

#include <getopt.h>
#include <stdlib.h>
#include <string.h>
#include <stdio.h>

#include <rte_common.h>
#include <rte_ethdev.h>
#include <cmdline_parse_etheraddr.h>

#include "nf-util.h"
#include "nf-log.h"

const uint16_t DEFAULT_LAN = 1;
const uint16_t DEFAULT_WAN = 0;
const uint64_t DEFAULT_RATE = 1000000; // 1MB/s
const uint64_t DEFAULT_BURST = 100000; // 100kB
const uint32_t DEFAULT_CAPACITY = 128; // IPs

#define PARSE_ERROR(format, ...)                                               \
  nf_config_usage();                                                           \
  rte_exit(EXIT_FAILURE, format, ##__VA_ARGS__);

void nf_config_init(int argc, char **argv) {
  // Set the default values
  config.lan_device = DEFAULT_LAN;
  config.wan_device = DEFAULT_WAN;
  config.rate = DEFAULT_RATE;             // B/s
  config.burst = DEFAULT_BURST;           // B
  config.dyn_capacity = DEFAULT_CAPACITY; // MAC addresses

  unsigned nb_devices = rte_eth_dev_count();

  struct option long_options[] = { { "lan", required_argument, NULL, 'l' },
                                   { "wan", required_argument, NULL, 'w' },
                                   { "rate", required_argument, NULL, 'r' },
                                   { "burst", required_argument, NULL, 'b' },
                                   { "capacity", required_argument, NULL, 'c' },
                                   { NULL, 0, NULL, 0 } };

  int opt;
  while ((opt = getopt_long(argc, argv, "l:w:r:b:c:", long_options, NULL)) !=
         EOF) {
    switch (opt) {
      case 'l':
        config.lan_device = nf_util_parse_int(optarg, "lan", 10, '\0');
        if (config.lan_device < 0 || config.lan_device >= nb_devices) {
          PARSE_ERROR("Invalid LAN device.\n");
        }
        break;

      case 'w':
        config.wan_device = nf_util_parse_int(optarg, "wan", 10, '\0');
        if (config.wan_device < 0 || config.wan_device >= nb_devices) {
          PARSE_ERROR("Invalid WAN device.\n");
        }
        break;

      case 'r':
        config.rate = nf_util_parse_int(optarg, "rate", 10, '\0');
        if (config.rate == 0) {
          PARSE_ERROR("Policer rate must be strictly positive.\n");
        }
        break;

      case 'b':
        config.burst = nf_util_parse_int(optarg, "burst", 10, '\0');
        if (config.burst == 0) {
          PARSE_ERROR("Policer burst size must be strictly positive.\n");
        }
        break;

      case 'c':
        config.dyn_capacity = nf_util_parse_int(optarg, "capacity", 10, '\0');
        if (config.dyn_capacity <= 0) {
          PARSE_ERROR("Flow table size must be strictly positive.\n");
        }
        break;

      default:
        PARSE_ERROR("Unknown option %c", opt);
    }
  }

  // Reset getopt
  optind = 1;
}

void nf_config_usage(void) {
  NF_INFO("Usage:\n"
          "[DPDK EAL options] --\n"
          "\t--lan <device>: LAN device,"
          " default: %" PRIu16 ".\n"
          "\t--wan <device>: WAN device,"
          " default: %" PRIu16 ".\n"
          "\t--rate <rate>: policer rate in bytes/s,"
          " default: %" PRIu64 ".\n"
          "\t--burst <size>: policer burst size in bytes,"
          " default: %" PRIu64 ".\n"
          "\t--capacity <n>: policer table capacity,"
          " default: %" PRIu32 ".\n",
          DEFAULT_LAN, DEFAULT_WAN, DEFAULT_RATE, DEFAULT_BURST,
          DEFAULT_CAPACITY);
}

void nf_config_print(void) {
  NF_INFO("\n--- Policer Config ---\n");

  NF_INFO("LAN Device: %" PRIu16, config.lan_device);
  NF_INFO("WAN Device: %" PRIu16, config.wan_device);
  NF_INFO("Rate: %" PRIu64, config.rate);
  NF_INFO("Burst: %" PRIu64, config.burst);
  NF_INFO("Capacity: %" PRIu16, config.dyn_capacity);

  NF_INFO("\n--- ------ ------ ---\n");
}
