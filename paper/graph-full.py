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

numbers = {}
all_vals = []
max_tput = 0
max_99lat = 0
MAXLAT = 100
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

# Find outlier limit, i.e., first one very far from previous
limit = 0
after_limit = 0
all_vals.sort()
DIFF = 10
OFFSET = 0.5
for idx in range(1, len(all_vals)):
  if all_vals[idx] - all_vals[idx - 1] >= DIFF:
    limit = all_vals[idx - 1] + OFFSET
    after_limit = all_vals[idx] - OFFSET
    break

import matplotlib as mpl
mpl.use('Agg') # avoid the need for an X server
import matplotlib.pyplot as plt
# Avoid margins for axes
plt.rcParams['axes.ymargin'] = 0
plt.rcParams['axes.xmargin'] = 0

axes = []
max_val = max_99lat + 0.5
if limit == 0:
  fig, ax = plt.subplots(1, 1)
  axes = [ax]
  ax.set_ylim(bottom=0, top=max_val)
else:
  height_ratio=4
  fig, (ax1, ax2) = plt.subplots(2, 1, sharex=True, gridspec_kw={'height_ratios': [1, height_ratio]})
  axes = [ax1, ax2]
  # Remove bottom spine for the outlier
  ax1.spines['bottom'].set_visible(False)
  # see https://matplotlib.org/examples/pylab_examples/broken_axis.html
  ax1.set_ylim(bottom=after_limit, top=max_val)
  ax1.ticklabel_format(useOffset=False) # prevent scientific notation
  ax2.set_ylim(0, limit)
  ax1.xaxis.set_ticks_position('none')
  d = .015 # size of the diagonal lines in the axes cordinates
  kwargs = dict(transform=ax1.transAxes, color='k', clip_on=False)
  ax1.plot((-d, +d), (-d, +d), **kwargs)
  # because our plots have different heights, we must be a little clever... the offset is a magic value found by trial and error
  ax1.plot((-d, +d), (-d-0.24, +d-0.24), **kwargs)
  ax1.set_zorder(1000) # required so the bottom "cut" diagonal line shows properly
  plt.subplots_adjust(hspace=0.09)

# Remove top/right spines
for ax in axes:
  ax.spines['top'].set_visible(False)
  ax.spines['right'].set_visible(False)

# Plot the data
for ax in axes:
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

plt.savefig(get_output_folder(kind, nf) + '/full-' + str(perc) + '.svg', bbox_inches='tight', pad_inches=0)
