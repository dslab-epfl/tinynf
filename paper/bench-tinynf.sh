sudo pkill -9 tinynf # we shouldn't need this but in case it errored...
cd ../benchmarking

for kind in throughput latency; do
  ./bench.sh ~/tinynf/code $kind 4
done
