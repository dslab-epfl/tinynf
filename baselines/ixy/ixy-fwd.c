// This is a modified copy of ixy's "ixy-fwd.c" sample app: it accepts a batch size as a preprocessor define, does not print statistics, and does not use interrupts.
// The "forward" method itself is unmodified besides changing "BATCH_SIZE" to "IXY_BATCH_SIZE".

#include "memory.h"
#include "driver/device.h"

static void forward(struct ixy_device* rx_dev, uint16_t rx_queue, struct ixy_device* tx_dev, uint16_t tx_queue) {
	struct pkt_buf* bufs[IXY_BATCH_SIZE];
	uint32_t num_rx = ixy_rx_batch(rx_dev, rx_queue, bufs, IXY_BATCH_SIZE);
	if (num_rx > 0) {
		// touch all packets, otherwise it's a completely unrealistic workload if the packet just stays in L3
		for (uint32_t i = 0; i < num_rx; i++) {
			bufs[i]->data[1]++;
		}
		uint32_t num_tx = ixy_tx_batch(tx_dev, tx_queue, bufs, num_rx);
		// there are two ways to handle the case that packets are not being sent out:
		// either wait on tx or drop them; in this case it's better to drop them, otherwise we accumulate latency
		for (uint32_t i = num_tx; i < num_rx; i++) {
			pkt_buf_free(bufs[i]);
		}
	}
}

int main(int argc, char* argv[]) {
	struct ixy_device* dev1 = ixy_init(argv[1], 1, 1, 0);
	struct ixy_device* dev2 = ixy_init(argv[2], 1, 1, 0);

	while (true) {
		forward(dev1, 0, dev2, 0);
		forward(dev2, 0, dev1, 0);
	}
}
