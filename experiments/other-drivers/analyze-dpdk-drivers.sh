#!/bin/sh

hw_count=$(sed -e '0,/| Name/d' dpdk-drivers.md | tail -n+2 | grep '|\s*yes\s*|' | wc -l)
desc_count=$(sed -e '0,/| Name/d' dpdk-drivers.md | tail -n+2 | grep '|\s*yes\s*|\s*yes\s*|' | wc -l)

printf 'DPDK has %d drivers for NIC dataplane hardware, of which %d use descriptors (%.0f%%)\n' $hw_count $desc_count $(echo "scale=2; $desc_count / $hw_count * 100" | bc)
