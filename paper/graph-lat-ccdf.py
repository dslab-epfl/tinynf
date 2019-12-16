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
values = [[float(l.strip())/1000.0 for l in open(get_lat_dir(kind, nf, arg[0], arg[1]), 'r')] for arg in args]

import matplotlib as mpl
mpl.use('Agg') # avoid the need for an X server

import matplotlib.pyplot as plt
width_ratio=4
fig, (ax1, ax2) = plt.subplots(1, 2, sharey=True, gridspec_kw={'width_ratios': [width_ratio, 1]})

# Remove top/right spines for both, and left for the outlier one
for ax in [ax1, ax2]:
  ax.spines['top'].set_visible(False)
  ax.spines['right'].set_visible(False)
ax2.spines['left'].set_visible(False)

# Plot the data in both
for ax in [ax1, ax2]:
  for array, key in zip(values, keys):
    ax.hist(array, 10*len(array), density=True, histtype='step', cumulative=True, label=key, color=get_color(key))
    # Remove the pointless horizontal line at the end, see https://stackoverflow.com/a/52921726/3311770
    for poly in ax.get_children():
      if isinstance(poly, mpl.patches.Polygon):
        poly.set_xy(poly.get_xy()[:-1])

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

if limit == 0:
  print("idk how to handle this")
  sys.exit(1)
else:
  # see https://matplotlib.org/examples/pylab_examples/broken_axis.html
  ax2.set_xlim(left=after_limit)
  ax1.set_xlim(0, limit)
  ax2.yaxis.set_ticks_position('none')
  d = .015 # size of the diagonal lines in the axes cordinates
  kwargs = dict(transform=ax2.transAxes, color='k', clip_on=False)
  ax2.plot((-d, +d), (-d, +d), **kwargs)
  # because our plots have different widths, we must be a little clever... the offset is a magic value found by trial and error
  ax2.plot((-d-0.24, +d-0.24), (-d, +d), **kwargs)
  ax2.set_zorder(1000) # required so the bottom "cut" diagonal line shows properly
  plt.subplots_adjust(wspace=0.1)

fig.suptitle(get_title(kind, nf), y=0.9) # put the title inside the plot to save space
fig.text(0.5, 0.02, 'Latency (us)', ha='center')
fig.text(0.02, 0.5, 'Cumulative probability', va='center', rotation='vertical')
plt.legend(loc='center right', handletextpad=0.3)
plt.savefig(get_output_filename(kind, nf, 'latencies.pdf'), bbox_inches='tight')
