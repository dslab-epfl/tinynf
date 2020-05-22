#!/usr/bin/python3

import matplotlib as mpl
import common
import pathlib
import sys

if len(sys.argv) < 3:
  print('[ERROR] Args: <title> <file>*')
  sys.exit(1)

title = sys.argv[1]
files = sys.argv[2:]

values = {}
max_lat = 0
for file in files:
  path = pathlib.Path(file)
  lats = [float(l) / 1000.0 for l in path.read_text().splitlines()]
  lats = sorted(lats)
  max_lat = max(max_lat, lats[-1])
  values[file] = lats

plt, ax, fig = common.get_pyplot_ax_fig(title, figsize=[6.2, 2.4]) # half usual height
ax.set_ylim(bottom=0, top=1.02) # ensure top lines are visible, not exactly 1
#plt.yscale('linear')
ax.set_xlim(0, max_lat)
ax.grid(True, color='xkcd:light grey')
ax.set_axisbelow(True) # ensure grid is below data

lines = []
for (folder, lats) in values.items():
  (color, label, marker) = common.get_color_label_marker(folder) # this works with folder names due to how we determine this info...
  ax.hist(lats, 10 * len(lats), density=True, histtype='step', cumulative=True, color=color, linewidth=1.8)
  # Remove the pointless horizontal line at the end, see https://stackoverflow.com/a/52921726/3311770
  for poly in ax.get_children():
    if isinstance(poly, mpl.patches.Polygon):
      poly.set_xy(poly.get_xy()[:-1])
  lines.append(mpl.lines.Line2D([], [], color=color, label=label))

# Custom legend so we get lines and not rectangles
plt.legend(handles=lines, loc='center right', handletextpad=0.3, borderaxespad=0)

# Custom ax labels
fig.text(0.5, -0.04, 'Latency (\u03BCs)', ha='center')
fig.text(0.02, 0.5, 'Cumulative probability', va='center', rotation='vertical')
common.save_plot(plt, 'Latencies: ' + title)
