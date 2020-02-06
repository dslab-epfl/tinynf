#!/usr/bin/python3

from common import *
import itertools
import pathlib
import sys

if len(sys.argv) < 4: # script itself + args
  print('[ERROR] Please provide the kind, NF, then at least one "key/param" to graph')
  sys.exit(1)

kind = sys.argv[1]
nf = sys.argv[2]
args = [arg.split('/') for arg in sys.argv[3:]]

keys = [arg[0] for arg in args]
keys = ['custom' if k == 'custom, simple' else k for k in keys]
values = [[float(l.strip())/1000.0 for l in pathlib.Path(get_output_folder(kind, nf), arg[0], arg[1], 'latencies', '0').read_text().splitlines()] for arg in args]

values = [sorted(vals) for vals in values]
values = [vals[0:int(len(vals)/10000*9999)] for vals in values] # Primorac 2017, values after 99.99% are inaccurate

# Find outlier limit, i.e., first one very far from previous
limit = 0
after_limit = 0
all_vals = list(itertools.chain.from_iterable(values))
all_vals.sort()
for idx in range(1, len(all_vals)):
  if all_vals[idx] - all_vals[idx - 1] >= 20:
    limit = all_vals[idx - 1] + 1
    after_limit = all_vals[idx] - 5
    break

import matplotlib as mpl
mpl.use('Agg') # avoid the need for an X server
import matplotlib.pyplot as plt
# Avoid margins for axes
plt.rcParams['axes.ymargin'] = 0
plt.rcParams['axes.xmargin'] = 0

axes = []
if limit == 0:
  fig, ax = plt.subplots(1, 1, figsize=[6.4, 2.4]) # half the usual height
  axes = [ax]
  ax.set_xlim(0, max([max(arr) for arr in values]))
else:
  width_ratio=4
  fig, (ax1, ax2) = plt.subplots(1, 2, sharey=True, gridspec_kw={'width_ratios': [width_ratio, 1]})
  axes = [ax1, ax2]
  # Remove the left spine for the outlier one
  ax2.spines['left'].set_visible(False)
  # see https://matplotlib.org/examples/pylab_examples/broken_axis.html
  ax2.set_xlim(after_limit, max([max(arr) for arr in values]))
  ax1.set_xlim(0, limit)
  ax2.yaxis.set_ticks_position('none')
  d = .015 # size of the diagonal lines in the axes cordinates
  kwargs = dict(transform=ax2.transAxes, color='k', clip_on=False)
  # -0.01 to not hide data underneath the lines
  ax2.plot((-d-0.01, +d-0.01), (-d, +d), **kwargs)
  # because our plots have different widths, we must be a little clever... the offset is a magic value found by trial and error
  ax2.plot((-d-0.24, +d-0.24), (-d, +d), **kwargs)
  # add cut lines for the grid
  kwargs.update(color='xkcd:light grey')
  for offset in [0.2, 0.4, 0.6, 0.8, 1]:
    ax2.plot((-d-0.01, +d-0.01), (-d+offset, +d+offset), **kwargs)
    ax2.plot((-d-0.24, +d-0.24), (-d+offset, +d+offset), **kwargs)
  ax2.set_zorder(1000) # required so the bottom "cut" diagonal line shows properly
  plt.subplots_adjust(wspace=0.1)

# Remove top/right spines
for ax in axes:
    ax.spines['top'].set_visible(False)
    ax.spines['right'].set_visible(False)

# Ensure the top lines are visible
for ax in axes:
  ax.set_ylim(0, 1.02)

# Plot the data
for ax in axes:
  for array, key in zip(values, keys):
    ax.hist(array, 10*len(array), density=True, histtype='step', cumulative=True, color=get_color(key), linewidth=1.8)
    # Remove the pointless horizontal line at the end, see https://stackoverflow.com/a/52921726/3311770
    for poly in ax.get_children():
      if isinstance(poly, mpl.patches.Polygon):
        poly.set_xy(poly.get_xy()[:-1])

for ax in axes:
  ax.grid(True, color='xkcd:light grey')
  ax.set_axisbelow(True) # ensure the grid ends up below the data

def real_label(key):
  if key == 'custom': return 'TinyNF'
  if key == 'original': return 'DPDK'
  return 'WRONG_LABEL'

# Custom legend so we get lines and not rectangles
import matplotlib.lines as mlines
lines = [mlines.Line2D([], [], color=get_color(key), label=real_label(key)) for key in keys]
plt.legend(handles=lines, loc='center right', handletextpad=0.3, borderaxespad=0)

fig.suptitle(get_title(kind, nf), y=0.85)
fig.text(0.5, -0.04, 'Latency (us)', ha='center')
fig.text(0.02, 0.5, 'Cumulative probability', va='center', rotation='vertical')
plt.savefig(get_output_folder(kind, nf) + '/latencies-cdf.svg', bbox_inches='tight', pad_inches=0)
