#!/bin/sh

if [ -z "$VIGOR_DIR" ]; then
  echo 'You do not have the VIGOR_DIR environment variable, which should point to a folder in which the "vigor" folder is.'
fi

echo "DPDK NIC registers in Vigor models, excluding stats: $(grep -F 'REG(' $VIGOR_DIR/vigor/libvig/models/hardware.c | grep -v DEV_REG | grep -v define | grep -v stat_regs | wc -l)"
echo "DPDK NIC stats registers: 144 (manually counted; 115 in stat_regs, 7 in stat_regs_rw, 22 in stat_regs_ro)"

echo "TinyNF PCI registers: $(grep 'IXGBE_PCIREG_.*0x' ../../code/net/82599/ixgbe.c | grep -v IXGBE_PCIREG_WRITE | wc -l)"
echo "TinyNF registers: $(grep 'IXGBE_REG_.*0x' ../../code/net/82599/ixgbe.c | grep -v IXGBE_REG_WRITE | wc -l)"
