#!/usr/bin/python3

from common import *
import sys

if len(sys.argv) < 4: # script itself + args
  print('[ERROR] Please provide the kind, NF, then at least one "key/period" to graph')
  sys.exit(1)

kind = sys.argv[1]
nf = sys.argv[2]
args = [arg.split('/') for arg in sys.argv[3:]]

keys = [arg[0] for arg in args]
values = [[float(l.strip()) / 1000 for l in open(get_lat_dir(kind, nf, arg[0], arg[1]), 'r')] for arg in args]

import matplotlib as mpl
mpl.use('Agg') # avoid the need for an X server
import matplotlib.pyplot as plt

# Find outlier limit, i.e., first one very far from previous
limit = 0
after_limit = 0
for vals in values:
  for idx in range(1, len(vals)):
    if vals[idx] - vals[idx - 1] >= 10:
      limit = vals[idx - 1] + 1
      after_limit = vals[idx]
      break
  else:
    continue # we didn't break
  break # we did break out of the inner loop

axes = []
if limit == 0:
  fig, ax = plt.subplots(1, 1)
  axes = [ax]
  ax.set_ylim(0, max([max(arr) for arr in values]))
else:
  height_ratio=4
  fig, (ax1, ax2) = plt.subplots(2, 1, sharex=True, gridspec_kw={'height_ratios': [1, height_ratio]})
  axes = [ax1, ax2]
  # Remove bottom spine for the outlier
  ax1.spines['bottom'].set_visible(False)
  # see https://matplotlib.org/examples/pylab_examples/broken_axis.html
  ax1.set_ylim(bottom=after_limit)
  ax2.set_ylim(0, limit)
  ax1.xaxis.set_ticks_position('none')
  d = .015 # size of the diagonal lines in the axes cordinates
  kwargs = dict(transform=ax1.transAxes, color='k', clip_on=False)
  ax1.plot((-d, +d), (-d, +d), **kwargs)
  # because our plots have different heights, we must be a little clever... the offset is a magic value found by trial and error
  ax1.plot((-d, +d), (-d-0.24, +d-0.24), **kwargs)
  ax1.set_zorder(1000) # required so the bottom "cut" diagonal line shows properly
  plt.subplots_adjust(hspace=0.1)

# Remove top/right spines
for ax in axes:
  ax.spines['top'].set_visible(False)
  ax.spines['right'].set_visible(False)

# Plot the data
for ax in axes:
  plot = ax.boxplot(values, whis='range', labels=keys, patch_artist=True)
  for box, key in zip(plot['boxes'], keys):
    box.set_facecolor(get_color(key))

fig.suptitle(get_title(kind, nf), y=0.85) # put the title inside the plot to save space
plt.ylabel('Latency (us)')
plt.savefig(get_output_filename(kind, nf, 'latencies.pdf'), bbox_inches='tight')
