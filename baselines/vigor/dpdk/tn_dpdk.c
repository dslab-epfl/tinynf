#include <tn_dpdk.h>

struct tn_dpdk_device tn_dpdk_devices[TN_DPDK_DEVICES_MAX_COUNT];
struct tn_pci_device tn_dpdk_pci_devices[TN_DPDK_DEVICES_MAX_COUNT];
uint16_t tn_dpdk_devices_count;
