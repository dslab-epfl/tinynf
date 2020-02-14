Repository structure:
- `baselines` contains other repositories that serve as baselines to measure performance
- `benchmarking` contains benchmarking scripts
- `code` contains the actual code:
  - `env` is the environment abstraction layer
  - `net` is the network abstraction, whose implementation is the driver
  - `util` contains utility code
  - `tinynf.c` shows an example of how to use the driver
- `paper` contains scripts and data used for the paper (but not the paper itself)
- `shims` contain shim layers used for the baselines above
