#include "device.h"

// Packet processing
int main()
{
	return tn_dev_init();
/*	int init_ret = nf_init();
	if (init_ret != 0) {
		return init_ret;
	}

	while(true) {
		tn_recv();
		tn_send(); // or tn_drop();
	}*/
}
