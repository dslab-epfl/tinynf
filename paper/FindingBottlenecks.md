# Finding CPU bottlenecks on Linux

This is based on [a blog post by Denis Bakhvalov](https://easyperf.net/blog/2019/02/09/Top-Down-performance-analysis-methodology).

You'll need two machines, same setup as the benchmarks.

Ensure your Linux kernel supports 'perf'.

Download `pmu-tools`, we'll specifically need `toplev`: https://github.com/andikleen/pmu-tools/wiki/toplev-manual


## Compiling

Make with `TN_STRIP=true TN_DEBUG=0 TN_CFLAGS=-g make` to disable all debugging but keep symbols (which will be used to locate the bottleneck statements later).

You may also want to add `-DIXGBE_PIPE_MAX_SENDS=1` to `TN_CFLAGS`, or similar, to avoid unused pipes during profiling.

LTO is also a good idea, with `-flto` in `TN_CFLAGS` and `TN_LDFLAGS`.


## Finding the bottleneck

On the 'tester' machine, run the benchmark script in flood mode, e.g. `sudo ./moon-gen/build/MoonGen ./tinynf-benchmarking/bench-moongen.lua flood 4`

Run the NF using toplev, e.g. `sudo ~/pmu-tools/toplev.py -l1 -v --no-desc taskset -c 6 ./tinynf 06:00.0 06:00.1`

After a minute or so, Ctrl+C the NF to see what toplev prints.

In our case, "Backend_Bound" should be ~70% of the total, with a bit over 20% of "Retiring".

Drill down more using `-l2` or `-l3` instead of `-l1` in the toplev arguments.

Using the [TMA metrics](https://download.01.org/perfmon/TMA_Metrics.xlsx) table, figure out which event you should be watching for with the "locate with" column (you'll need to know which revision your CPU is using, e.g. "IVB" for Ivy Bridge). Find the corresponding event in "perf list".

For instance, if toplev indicates the bottleneck is "Backend_Bound.Memory_Bound.Store_Bound" and your CPU is Ivy Bridge, the perf metric is "mem_uops_retired.all_stores".


## Locating bottleneck instructions/statements

You can then run perf asking for a specific event and canceling the effect of skid with `ppp`, e.g. `sudo perf record -e cpu/event=mem_uops_retired.all_stores/ppp taskset -c 6 ./tinynf 06:00.0 06:00.1`.

After a while, stop with Ctrl+C, then use `sudo perf report -n --stdio` to see where the samples are from, and `sudo perf annotate --stdio -M intel foo` to see where the instructions are in function `foo`.
