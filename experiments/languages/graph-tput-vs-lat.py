#!/usr/bin/python3

import math
import os
import pathlib
import statistics
import sys

sys.path.append("..")
import common


THIS_DIR = os.path.dirname(os.path.realpath(__file__))

if len(sys.argv) < 3:
  print('Args: <name> <folder name in results/>*')
  sys.exit(1)

name = sys.argv[1]

perc = 50
perc_str = 'Median'
perc_comp = 99
perc_bottom = 1
perc_top = 99

nfs = sys.argv[2:]

def lats_at_perc(lats, perc):
  return [(tput, common.percentile(ls, perc)) for (tput, ls) in lats]

numbers = {}
all_vals = []
max_tput = 0
lats_comp = []
for nf in nfs:
  nf_folder = THIS_DIR + '/results/' + nf

  lats_folder = pathlib.Path(nf_folder, 'latencies')
  lats = [(float(lat_file.name) / 1000, [float(l) / 1000.0 for l in lat_file.read_text().splitlines()]) for lat_file in lats_folder.glob('*')]
  lats = sorted(lats, key=lambda t: t[0])

  tput = lats[-1][0]

  tput_zeroloss_file = pathlib.Path(nf_folder, 'throughput-zeroloss')
  tput_zeroloss = float(tput_zeroloss_file.read_text()) if tput_zeroloss_file.exists() else math.inf

  lats_bot = lats_at_perc(lats, perc_bottom)
  lats_top = lats_at_perc(lats, perc_top)
  lats_perc = lats_at_perc(lats, perc)
  lats_comp += lats_at_perc(lats, perc_comp)

  numbers[nf] = (lats_bot, lats_top, lats_perc, lats_comp, tput_zeroloss, lats)
  max_tput = max(max_tput, tput)

all_lats_comp = [l for val in numbers.values()
                 for (t, l) in val[3]
                 for l in (t, l)]
median_lat_comp = statistics.median(all_lats_comp)

plt, ax, _ = common.get_pyplot_ax_fig()
ax.set_ylim(bottom=0, top=median_lat_comp * 2)
ax.set_xlim(0, math.ceil(max_tput) + 0.2) #20.2) # just a little bit of margin to not hide the right side of the markers

# We want a straight line up to tput_zeroloss, then a dashed line after that, so we draw 2 lines
# And we want the lines to be opaque while the dots should be non-opaque, for clarity, so we draw them separately
for nf, val in numbers.items():
  (lats_bot, lats_top, lats, _, _, _) = val

  (color, marker) = common.get_color_and_marker(nf)

  y_bot = [l for (t, l) in lats_bot]
  y_top = [l for (t, l) in lats_top]
  all_x = [t for (t, l) in lats]
  all_y = [l for (t, l) in lats]

  ax.plot(all_x, all_y, color=color, alpha=0.4, linestyle='solid')
  ax.fill_between(all_x, y_bot, all_y, color=color, alpha=0.15)
  ax.fill_between(all_x, all_y, y_top, color=color, alpha=0.15)
  ax.scatter(all_x, all_y, color=color, label=nf, marker=marker, s=60)

plt.xlabel('Throughput (Gb/s)')
plt.ylabel(perc_str + ' latency (\u03BCs)')
plt.legend(loc='upper left', handletextpad=0.3, borderaxespad=0.08, edgecolor='white', frameon=False)

common.save_plot(plt, name)
