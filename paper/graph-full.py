#!/usr/bin/python3

import common
import math
import os
import pathlib
import statistics
import sys

THIS_DIR = os.path.dirname(os.path.realpath(__file__))

if len(sys.argv) < 4:
  print('Args: <title> <latency percentile> <nf folder name>*')
  sys.exit(1)

title = sys.argv[1]

perc = int(sys.argv[2])
perc_str = str(perc) + 'th percentile'
if perc == 50:
  perc_str = 'Median'

nfs = sys.argv[3:]

def lats_at_perc(lats, perc):
  return [(tput, common.percentile(ls, perc)) for (tput, ls) in lats]

numbers = {}
all_vals = []
max_tput = 0
lats_99th = []
for nf in nfs:
  nf_folder = THIS_DIR + '/results/' + nf

  lats_folder = pathlib.Path(nf_folder, 'latencies')
  lats = [(float(lat_file.name), [float(l) / 1000.0 for l in lat_file.read_text().splitlines()]) for lat_file in lats_folder.glob('*')]
  lats = sorted(lats, key=lambda t: t[0])

  tput = lats[-1][0]

  tput_zeroloss_file = pathlib.Path(nf_folder, 'throughput-zeroloss')
  tput_zeroloss = float(tput_zeroloss_file.read_text()) if tput_zeroloss_file.exists() else math.inf

  lats_perc = lats_at_perc(lats, perc)
  lats_99th += lats_at_perc(lats, 99)

  numbers[nf] = (lats_perc, lats_99th, tput_zeroloss)
  max_tput = max(max_tput, tput)

# Figure out a good max Y; if the 99th lat is more stable, use that so the graphs compare better; add some % anyway since we want to show most values
all_lats_perc = [l for val in numbers.values()
                 for (t, l) in val[0]
                 for l in (t, l)]
all_lats_99th = [l for val in numbers.values()
                 for (t, l) in val[1]
                 for l in (t, l)]
median_lat_perc = statistics.median(all_lats_perc)
median_lat99th = statistics.median(all_lats_99th)
lat_lim = max(median_lat_perc, median_lat99th) * 2

plt, ax = common.get_pyplot_ax(title)
ax.set_ylim(bottom=0, top=lat_lim)
ax.set_xlim(0, max_tput + 200) # just a lil bit of margin

# We want a straight line up to tput_zeroloss, then a dashed line after that, so we draw 2 lines
# And we want the lines to be opaque while the dots should be non-opaque, for clarity, so we draw them separately
for nf, val in numbers.items():
  (lats, _, tput_zeroloss) = val

  (color, label, marker) = common.get_color_label_marker(nf)

  zeroloss_x = [t for (t, l) in lats if t <= tput_zeroloss]
  zeroloss_y = [l for (t, l) in lats if t <= tput_zeroloss]
  if len(zeroloss_x) > 0:
    ax.plot(zeroloss_x, zeroloss_y, color=color, alpha=0.4, linestyle='solid')

  loss_x = [t for (t, l) in lats if t > tput_zeroloss]
  loss_y = [l for (t, l) in lats if t > tput_zeroloss]
  if len(loss_x) > 0:
    # ensure the line starts from where the other one ends
    if len(zeroloss_x) > 0:
      loss_x = [zeroloss_x[-1]] + loss_x
      loss_y = [zeroloss_y[-1]] + loss_y
    ax.plot(loss_x, loss_y, color=color, alpha=0.3, linestyle='dashed')

  all_x = [t for (t, l) in lats]
  all_y = [l for (t, l) in lats]
  ax.scatter(all_x, all_y, color=color, label=label, marker=marker)

plt.xlabel('Throughput (Mb/s)')
plt.ylabel(perc_str + ' latency (\u03BCs)')
plt.legend(loc='upper left', handletextpad=0.3)

common.save_plot(plt, 'Full, ' + title + ', ' + perc_str)
