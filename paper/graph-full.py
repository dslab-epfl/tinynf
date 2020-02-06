#!/usr/bin/python3

from common import *
import glob
import itertools
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

SAMESCALE=False
if nf == 'nop': SAMESCALE=True
numbers = {}
all_vals = []
max_tput = 0
max_99lat = 0
MAXLAT = 400
for key_folder in [f for f in sorted(glob.glob(get_output_folder(kind, nf) + '/*')) if os.path.isdir(f)]:
  for param_folder in glob.glob(key_folder + '/*'):
    param = int(os.path.basename(param_folder))
    latencies = [(float(latf.name), [float(l) / 1000.0 for l in latf.read_text().splitlines()]) for latf in pathlib.Path(param_folder, 'latencies').glob('*')]
    these_latencies = [(t, percentile(ls, perc)) for (t, ls) in latencies if percentile(ls, perc) <= MAXLAT]
    key = os.path.basename(key_folder)
    if key == 'shim, simple': continue
    if key == 'custom, simple': key = 'custom'
    if param == 64:
      key += ', batching'
    numbers[key] = sorted(these_latencies, key=lambda t: t[0])
    all_vals += [l for (t, l) in these_latencies]
    max_tput = max(max_tput, max([t for (t, l) in these_latencies]))
    max_99lat = max(max_99lat, max([percentile(ls, 99) for (t, ls) in latencies if percentile(ls, 99) <= MAXLAT]))
numbers = dict(sorted(numbers.items()))

import matplotlib as mpl
mpl.use('Agg') # avoid the need for an X server
import matplotlib.pyplot as plt
# Avoid margins for axes
plt.rcParams['axes.ymargin'] = 0
plt.rcParams['axes.xmargin'] = 0

axes = []
if SAMESCALE: max_val = max_99lat + 0.5
else: max_val = 8 #max([max([l for _, l in ls]) for _, ls in numbers.items()]) * 1.03
fig, ax = plt.subplots(1, 1)
ax.set_ylim(bottom=0, top=max_val)

# Remove top/right spines
ax.spines['top'].set_visible(False)
ax.spines['right'].set_visible(False)

# Plot the data
ax.set_xlim(0, max_tput + 1000)
for key, latencies in numbers.items():
  color = get_color(key)
  x = [t for (t, l) in latencies]
  y = [l for (t, l) in latencies]
  # We want opaque dots with non-opaque lines, 'plot' doesn't seem to support that scenario alone
  ax.plot(x, y, color=color, alpha=0.3, linestyle='dashed')
  label = 'TinyNF'
  marker = 'o'
  if key == 'original':
    label = 'DPDK'
    marker = 'v'
  if key == 'original, batching':
    label = 'DPDK, batching'
    marker = '^'
  ax.scatter(x, y, color=color, label=label, marker=marker)

plt.xlabel('Throughput (Mbps)')
plt.ylabel(perc_str + ' latency (us)')
plt.legend(loc='upper left', handletextpad=0.3)
fig.suptitle(get_title(kind, nf), y=0.85)

plt.savefig(get_output_folder(kind, nf) + '/full-' + str(perc) + '.svg', bbox_inches='tight', pad_inches=0.01)
