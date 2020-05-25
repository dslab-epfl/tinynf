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

  unsigned nb_devices = rte_eth_dev_count_avail();
  if (nb_devices != 2) {
    rte_exit(EXIT_FAILURE, "Expected 2 devices, but was %u\n", nb_devices);
  }

  for (uint16_t device = 0; device < nb_devices; device++) {
    ret = init_device(device, mbuf_pool);
    if (ret != 0) {
      rte_exit(EXIT_FAILURE, "Cannot init device %u, ret=%d\n", (unsigned) device, ret);
    }
  }

  TN_PERF_PAPI_START();
  while(1) {
    for (uint64_t d = 0; d < 2; d++) {
      TN_PERF_PAPI_RESET();
      struct rte_mbuf* bufs[BATCH_SIZE];
      uint16_t nb_rx = rte_eth_rx_burst(d, 0, bufs, BATCH_SIZE);
      uint16_t nb_tx = rte_eth_tx_burst(1-d, 0, bufs, BATCH_SIZE);
      for (uint16_t n = nb_tx; n < nb_rx; n++) {
        rte_pktmbuf_free(bufs[n]);
      }
      TN_PERF_PAPI_RECORD(nb_rx);
    }
  }

  return 0;
}
