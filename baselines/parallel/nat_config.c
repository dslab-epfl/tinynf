#include "nat_config.h"

#include <getopt.h>
#include <stdlib.h>
#include <stdio.h>

#include <rte_common.h>
#include <rte_ethdev.h>

#include <cmdline_parse_etheraddr.h>
#include <cmdline_parse_ipaddr.h>

#include "nf.h"
#include "nf-util.h"

#define PARSE_ERROR(format, ...)                                               \
  nf_config_usage();                                                           \
  rte_exit(EXIT_FAILURE, format, ##__VA_ARGS__);

void nf_config_init(int argc, char **argv) {
  uint16_t nb_devices = rte_eth_dev_count();

  struct option long_options[] = {
    { "eth-dest", required_argument, NULL, 'm' },
    { "expire", required_argument, NULL, 't' },
    { "extip", required_argument, NULL, 'i' },
    { "lan-dev", required_argument, NULL, 'l' },
    { "max-flows", required_argument, NULL, 'f' },
    { "starting-port", required_argument, NULL, 's' },
    { "wan", required_argument, NULL, 'w' },
    { NULL, 0, NULL, 0 }
  };

  config.device_macs =
      (struct ether_addr *)calloc(nb_devices, sizeof(struct ether_addr));
  config.endpoint_macs =
      (struct ether_addr *)calloc(nb_devices, sizeof(struct ether_addr));

  // Set the devices' own MACs
  for (uint16_t device = 0; device < nb_devices; device++) {
    rte_eth_macaddr_get(device, &(config.device_macs[device]));
  }

  int opt;
  while ((opt = getopt_long(argc, argv, "m:e:t:i:l:f:p:s:w:", long_options,
                            NULL)) != EOF) {
    unsigned device;
    switch (opt) {
      case 'm':
        device = nf_util_parse_int(optarg, "eth-dest device", 10, ',');
        if (device >= nb_devices) {
          PARSE_ERROR("eth-dest: device %d >= nb_devices (%d)\n", device,
                      nb_devices);
        }

        optarg += 2;
        if (cmdline_parse_etheraddr(NULL, optarg,
                                    &(config.endpoint_macs[device]),
                                    sizeof(int64_t)) < 0) {
          PARSE_ERROR("Invalid MAC address: %s\n", optarg);
        }
        break;

      case 't':
        config.expiration_time =
            nf_util_parse_int(optarg, "exp-time", 10, '\0');
        if (config.expiration_time == 0) {
          PARSE_ERROR("Expiration time must be strictly positive.\n");
        }
        break;

      case 'i':;
        struct cmdline_token_ipaddr tk;
        tk.ipaddr_data.flags = CMDLINE_IPADDR_V4;

        struct cmdline_ipaddr res;
        if (cmdline_parse_ipaddr((cmdline_parse_token_hdr_t *)&tk, optarg, &res,
                                 sizeof(res)) < 0) {
          PARSE_ERROR("Invalid external IP address: %s\n", optarg);
        }

        config.external_addr = res.addr.ipv4.s_addr;
        break;

      case 'l':
        config.lan_main_device = nf_util_parse_int(optarg, "lan-dev", 10, '\0');
        if (config.lan_main_device >= nb_devices) {
          PARSE_ERROR("Main LAN device does not exist.\n");
        }
        break;

      case 'f':
        config.max_flows = nf_util_parse_int(optarg, "max-flows", 10, '\0');
        if (config.max_flows <= 0) {
          PARSE_ERROR("Flow table size must be strictly positive.\n");
        }
        break;

      case 's':
        config.start_port = nf_util_parse_int(optarg, "start-port", 10, '\0');
        break;

      case 'w':
        config.wan_device = nf_util_parse_int(optarg, "wan-dev", 10, '\0');
        if (config.wan_device >= nb_devices) {
          PARSE_ERROR("WAN device does not exist.\n");
        }
        break;

      default:
        PARSE_ERROR("Unknown option.\n");
        break;
    }
  }

  // Reset getopt
  optind = 1;
}

void nf_config_usage(void) {
}

void nf_config_print(void) {
}
