THIS_DIR := $(abspath $(dir $(lastword $(MAKEFILE_LIST))))

CARGO_FLAGS=
ifeq ($(TN_MODE),1)
CARGO_FLAGS=--features constgenerics
endif
ifeq ($(TN_MODE),2)
CARGO_FLAGS=--features queues
endif

# this --manifest-path trick is the equivalent to make -C, see https://github.com/rust-lang/cargo/issues/1485
build:
	@cargo build --manifest-path=$(THIS_DIR)/Cargo.toml $(CARGO_FLAGS) --release

format:
	@cargo fmt
