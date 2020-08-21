#!/bin/bash
set -eux

# Ensure the papi submodule is cloned
git submodule update --init --recursive

# Get the absolute path to papi, we'll use it when building and running things from other dirs
PAPI_DIR="$(readlink -e papi)"

# Build papi, but don't install it, we just want a local version
cd "$PAPI_DIR/src"
  ./configure
  make
cd -

cd ../code
  TN_CFLAGS='-DTN_DEBUG_PERF=100 -I "$PAPI_DIR/src" -L "$PAPI_DIR/src" -lpapi' make
  LD_LIBRARY_PATH="$PAPI_DIR/src" ./tinynf
cd -
