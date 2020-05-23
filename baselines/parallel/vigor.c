#include <inttypes.h>

#include <rte_common.h>
#include <rte_eal.h>
#include <rte_errno.h>
#include <rte_ethdev.h>
#include <rte_lcore.h>
#include <rte_mbuf.h>

#include "libvig/verified/boilerplate-util.h"
#include "libvig/verified/packet-io.h"
#include "nf-log.h"
#include "nf-util.h"
#include "nf.h"

#ifndef VIGOR_BATCH_SIZE
#  define VIGOR_BATCH_SIZE 1
#endif

// Number of RX/TX queues
static const uint16_t RX_QUEUES_COUNT = 1;
static const uint16_t TX_QUEUES_COUNT = 1;

// Queue sizes for receiving/transmitting packets
#if VIGOR_BATCH_SIZE == 1
static const uint16_t RX_QUEUE_SIZE = 128;
static const uint16_t TX_QUEUE_SIZE = 128;
#else
// NOT powers of 2 so that ixgbe doesn't use vector stuff
// but they have to be multiples of 8, and at least 32, otherwise the driver
// refuses
static const uint16_t RX_QUEUE_SIZE = 96;
static const uint16_t TX_QUEUE_SIZE = 96;
#endif

// Buffer count for mempools
static const unsigned MEMPOOL_BUFFER_COUNT = 256;

// --- Initialization ---
static int nf_init_device(uint16_t device, struct rte_mempool *mbuf_pool) {
  int retval;

  // device_conf passed to rte_eth_dev_configure cannot be NULL
  struct rte_eth_conf device_conf = {0};
  device_conf.rxmode.hw_strip_crc = 1;

  // Configure the device
  retval = rte_eth_dev_configure(device, RX_QUEUES_COUNT, TX_QUEUES_COUNT,
                                 &device_conf);
  if (retval != 0) {
    return retval;
  }

  // Allocate and set up TX queues
  for (int txq = 0; txq < TX_QUEUES_COUNT; txq++) {
    retval = rte_eth_tx_queue_setup(device, txq, TX_QUEUE_SIZE,
                                    rte_eth_dev_socket_id(device), NULL);
    if (retval != 0) {
      return retval;
    }
  }

  // Allocate and set up RX queues
  for (int rxq = 0; rxq < RX_QUEUES_COUNT; rxq++) {
    retval = rte_eth_rx_queue_setup(device, rxq, RX_QUEUE_SIZE,
                                    rte_eth_dev_socket_id(device),
                                    NULL, // default config
                                    mbuf_pool);
    if (retval != 0) {
      return retval;
    }
  }

  // Start the device
  retval = rte_eth_dev_start(device);
  if (retval != 0) {
    return retval;
  }

  // Enable RX in promiscuous mode, just in case
  rte_eth_promiscuous_enable(device);
  if (rte_eth_promiscuous_get(device) != 1) {
    return retval;
  }

  return 0;
}

// --- Per-core work ---

static void lcore_main() {
  unsigned lcore = rte_lcore_id();
  NF_INFO("Core %u forwarding packets.", lcore);
  uint16_t rx_id = lcore == 0 ? 0 : 1;
  uint16_t tx_id = lcore == 0 ? 1 : 0;
  while(1) {
    struct rte_mbuf *mbufs[VIGOR_BATCH_SIZE];
    struct rte_mbuf *mbufs_to_send[VIGOR_BATCH_SIZE];
    int mbuf_send_index = 0;
    uint16_t received_count = rte_eth_rx_burst(rx_id, 0, mbufs, VIGOR_BATCH_SIZE);
    for (uint16_t n = 0; n < received_count; n++) {
      uint8_t* packet = rte_pktmbuf_mtod(mbufs[n], uint8_t*);
      packet_state_total_length(packet, &(mbufs[n]->pkt_len));
      uint16_t dst_device = nf_process(mbufs[n]->port, packet, mbufs[n]->data_len, current_time());
      nf_return_all_chunks(packet);

      if (dst_device == VIGOR_DEVICE) {
        rte_pktmbuf_free(mbufs[n]);
      } else {
        mbufs_to_send[mbuf_send_index] = mbufs[n];
        mbuf_send_index++;
      }
    }

    uint16_t sent_count = rte_eth_tx_burst(tx_id, 0, mbufs_to_send, mbuf_send_index);
    for (uint16_t n = sent_count; n < mbuf_send_index; n++) {
      rte_pktmbuf_free(mbufs[n]);
    }
  }
}

// --- Main ---

int MAIN(int argc, char *argv[]) {
  // Initialize the Environment Abstraction Layer (EAL)
  int ret = rte_eal_init(argc, argv);
  if (ret < 0) {
    rte_exit(EXIT_FAILURE, "Error with EAL initialization, ret=%d\n", ret);
  }
  argc -= ret;
  argv += ret;

  // NF-specific config
  nf_config_init(argc, argv);
  nf_config_print();

  unsigned nb_devices = rte_eth_dev_count();
  if (nb_devices != 2) {
    printf("We assume there will be exactly 2 devices for our simple batching implementation.");
    exit(1);
  }

  struct rte_mempool *mbuf_pool = rte_pktmbuf_pool_create(
      "MEMPOOL",                         // name
      MEMPOOL_BUFFER_COUNT * nb_devices, // #elements
      128, // cache size (per-lcore, not useful in a single-threaded app)
      0, // application private area size
      RTE_MBUF_DEFAULT_BUF_SIZE, // data buffer size
      rte_socket_id()            // socket ID
  );
  if (mbuf_pool == NULL) {
    rte_exit(EXIT_FAILURE, "Cannot create mbuf pool: %s\n",
             rte_strerror(rte_errno));
  }

  // Initialize all devices
  for (uint16_t device = 0; device < nb_devices; device++) {
    ret = nf_init_device(device, mbuf_pool);
    if (ret == 0) {
      NF_INFO("Initialized device %" PRIu16 ".", device);
    } else {
      rte_exit(EXIT_FAILURE, "Cannot init device %" PRIu16 ", ret=%d", device,
               ret);
    }
  }

  if (!nf_init()) {
    rte_exit(EXIT_FAILURE, "Error initializing NF");
  }

  rte_eal_mp_remote_launch(lcore_main, NULL, CALL_MASTER);

  return 0;
}
