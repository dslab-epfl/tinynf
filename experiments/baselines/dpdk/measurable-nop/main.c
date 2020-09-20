#include <stdint.h>

#include <rte_common.h>
#include <rte_eal.h>
#include <rte_errno.h>
#include <rte_ethdev.h>
#include <rte_mbuf.h>

#include "util/perf.h"

#if BATCH_SIZE != 1
static const uint16_t RX_QUEUE_SIZE = 128;
static const uint16_t TX_QUEUE_SIZE = 512;
#else
static const uint16_t RX_QUEUE_SIZE = 160;
static const uint16_t TX_QUEUE_SIZE = 544;
#endif

static int init_device(uint16_t device, struct rte_mempool* mbuf_pool) {
  int retval;

  struct rte_eth_conf device_conf = {0};

  retval = rte_eth_dev_configure(device, 1, 1, &device_conf);
  if (retval != 0) {
    return retval;
  }

  retval = rte_eth_tx_queue_setup(device, 0, TX_QUEUE_SIZE, rte_eth_dev_socket_id(device), NULL);
  if (retval != 0) {
    return retval;
  }

  retval = rte_eth_rx_queue_setup(device, 0, RX_QUEUE_SIZE, rte_eth_dev_socket_id(device), NULL, mbuf_pool);
  if (retval != 0) {
    return retval;
  }

  retval = rte_eth_dev_start(device);
  if (retval != 0) {
    return retval;
  }

  rte_eth_promiscuous_enable(device);
  if (rte_eth_promiscuous_get(device) != 1) {
    return 1;
  }

  return 0;
}

int main(int argc, char* argv[]) {
  int ret = rte_eal_init(argc, argv);
  if (ret < 0) {
    rte_exit(EXIT_FAILURE, "Error with EAL initialization, ret=%d\n", ret);
  }
  argc -= ret;
  argv += ret;

  // we use what testpmd uses: (rx_desc_max + (nb_lcores * cache) + tx_desc_mac + max_burst) * max_ethports
  unsigned nb_mbuf = (2048 + 1 * 250 + 2048 + 512) * 32;
  struct rte_mempool* mbuf_pool = rte_pktmbuf_pool_create(
    "mempool",
    nb_mbuf,
    250,
    0, // app private area size
    RTE_MBUF_DEFAULT_BUF_SIZE,
    rte_socket_id()
  );
  if (mbuf_pool == NULL) {
    rte_exit(EXIT_FAILURE, "Cannot create mbuf pool, ret=%d\n", rte_errno);
  }

  uint16_t devices_count = 0;
  uint16_t device;
  uint16_t devices[2];
  RTE_ETH_FOREACH_DEV(device) {
    ret = init_device(device, mbuf_pool);
    if (ret != 0) {
      rte_exit(EXIT_FAILURE, "Cannot init device %u, ret=%d\n", (unsigned) device, ret);
    }
    if (devices_count == 0) { devices[0] = device; }
    else { devices[1] = device; }
    devices_count++;
  }
  if (devices_count != 2) {
    rte_exit(EXIT_FAILURE, "Expected 2 devices, but was %u\n", devices_count);
  }

  uint8_t lookup_table[256 * 256];
  for (uint64_t n = 0; n < sizeof(lookup_table)/sizeof(uint8_t); n++) {
    lookup_table[n] = (uint8_t) (n * 123);
  }

  struct rte_mbuf* bufs[BATCH_SIZE];
  uint16_t nb_rx;
  uint16_t nb_tx;
  TN_PERF_PAPI_INIT();
  while(1) {
    for (uint16_t d = 0; d < 2; d++) {
      TN_PERF_PAPI_RESET();
      nb_rx = rte_eth_rx_burst(devices[d], 0, bufs, BATCH_SIZE);
#ifdef TN_DEBUG_PERF_DOWRITE
      for (uint16_t n = 0; n < nb_rx; n++) {
        uint8_t* data = rte_pktmbuf_mtod(bufs[n], uint8_t*);
        data[0] = lookup_table[0];
        data[1] = lookup_table[1];
        data[2] = lookup_table[2];
        data[3] = lookup_table[3];
        data[4] = lookup_table[4];
        data[5] = lookup_table[5];
      }
#elif defined(TN_DEBUG_PERF_DOLOOKUP)
      for (uint16_t n = 0; n < nb_rx; n++) {
        uint8_t* data = rte_pktmbuf_mtod(bufs[n], uint8_t*);
        data[0] = lookup_table[(data[6] << 8) | data[7]];
        data[1] = lookup_table[(data[7] << 8) | data[6]];
        data[2] = lookup_table[(data[8] << 8) | data[9]];
        data[3] = lookup_table[(data[9] << 8) | data[8]];
        data[4] = lookup_table[(data[10] << 8) | data[11]];
        data[5] = lookup_table[(data[11] << 8) | data[10]];
      }
#endif
      nb_tx = rte_eth_tx_burst(devices[1-d], 0, bufs, nb_rx);
      for (uint16_t n = nb_tx; n < nb_rx; n++) {
        rte_pktmbuf_free(bufs[n]);
      }
      TN_PERF_PAPI_RECORD(nb_rx);
    }
  }

  return 0;
}
