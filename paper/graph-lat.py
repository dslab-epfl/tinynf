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
values = [[int(l.strip()) for l in open(get_lat_dir(kind, nf, arg[0], arg[1]), 'r')] for arg in args]

import matplotlib as mpl
mpl.use('Agg') # avoid the need for an X server

import matplotlib.pyplot as plt
height_ratio=4
fig, (ax1, ax2) = plt.subplots(2, 1, sharex=True, gridspec_kw={'height_ratios': [1, height_ratio]})

# Remove top/right spines for both, and bottom for the outlier one
for ax in [ax1, ax2]:
  ax.spines['top'].set_visible(False)
  ax.spines['right'].set_visible(False)
ax1.spines['bottom'].set_visible(False)

# Plot the data in both
for ax in [ax1, ax2]:
  plot = ax.boxplot(values, whis='range', labels=keys, patch_artist=True)
  for box, key in zip(plot['boxes'], keys):
    box.set_facecolor(get_color(key))

# Find outlier limit, i.e., first one very far from previous
limit = 0
after_limit = 0
for vals in values:
  for idx in range(1, len(vals)):
    if (vals[idx] // 1000) - (vals[idx - 1] // 1000) >= 10:
      limit = vals[idx - 1] // 1000 * 1000 + 1000
      after_limit = vals[idx] // 1000 * 1000
      break
  else:
    continue # we didn't break
  break # we did break out of the inner loop

if limit == 0:
  print("idk how to handle this")
  sys.exit(1)
else:
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

fig.suptitle(get_title(kind, nf), y=0.85) # put the title inside the plot to save space
plt.ylabel('Latency (ns)')
plt.savefig(get_output_filename(kind, nf, 'latencies.pdf'), bbox_inches='tight')
