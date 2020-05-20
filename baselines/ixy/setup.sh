#!/bin/sh

git submodule update --init --recursive

# Dependencies, as written in the ixy readme
sudo apt-get install -y build-essential cmake

# Remove the need for an IOMMU, other baselines don't use it
if ! grep -F 'PATCHED' ixy/src/driver/ixgbe.c >/dev/null; then
  sed -i 's|if (dev->ixy.vfio) {|if (0) { // PATCHED|' ixy/src/driver/ixgbe.c
fi

# Use our simplified ixy-fwd
cp ixy-fwd.c ixy/src/app/ixy-fwd.c
