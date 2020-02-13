#!/usr/bin/python3

from common import *
import glob
import pathlib
import os
import sys

this_dir = os.path.dirname(os.path.realpath(__file__))

if len(sys.argv) != 4:
  print('[ERROR] Please provide 3 arguments: kind, NF, latency percentile')
  sys.exit(1)

kind = sys.argv[1]
nf = sys.argv[2]
perc = int(sys.argv[3])
perc_str = str(perc) + 'th percentile'
if perc == 50:
  perc_str = 'Median'

numbers = {}
max_99th = 0
for key_folder in [f for f in sorted(glob.glob(get_output_folder(kind, nf) + '/*')) if os.path.isdir(f)]:
  key = os.path.basename(key_folder)
  params = {}
  for param_folder in glob.glob(key_folder + '/*'):
    param = int(os.path.basename(param_folder))
    throughput = int(pathlib.Path(param_folder, 'throughput').read_text().strip())
    latencies = [int(l) for l in sorted(pathlib.Path(param_folder, 'latencies').glob('*'))[-1].read_text().splitlines()]
    latency = int(percentile(latencies, perc))
    max_99th = max(max_99th, int(percentile(latencies, 99)))
    params[param] = { 'throughput': throughput, 'latency': latency }
  numbers[key] = dict(sorted(params.items()))

plt, ax = get_pyplot_ax(get_title(kind, nf))

for key, params in numbers.items():
  color = get_color(key)
  x = [v['throughput'] for v in params.values()]
  y = [v['latency'] for v in params.values()]
  # We want opaque dots with non-opaque lines, 'plot' doesn't seem to support that scenario alone
  ax.plot(x, y, color=color, alpha=0.3, linestyle='dashed')
  ax.scatter(x, y, color=color, label=key)

ax.set_xlim(left=0)
ax.set_ylim(bottom=0)
plt.xlabel('Max throughput with <0.1% loss (Mb/s)')
plt.ylabel(perc_str + ' latency (ns)')
plt.legend(loc='upper left', handletextpad=0.3)

plt.savefig(get_output_folder(kind, nf) + '/throughput-vs-latency-' + str(perc) + '.svg', bbox_inches='tight')
