#!/usr/bin/env python

import math
import os
import pathlib
import statistics
import sys

import matplotlib as mpl
import matplotlib.pyplot as plt

FILETYPE = '.svg'

# Some matplotlib config first:
mpl.use('Agg') # avoid the need for an X server
mpl.rcParams['axes.spines.right'] = False # no right spine
mpl.rcParams['axes.spines.top'] = False # no top spine
mpl.rc('font', **{'size': 11})
# HotCRP says to do that to avoid problems with embedded fonts
mpl.rcParams['pdf.fonttype'] = 42
mpl.rcParams['ps.fonttype'] = 42

# The max Y, so we don't waste space showing some extreme 95% percentile
YLIM = 10 # us

if len(sys.argv) < 3:
  print('Args: [--intro] <name> <folder name in results/>*')
  sys.exit(1)
INTRO=False
if sys.argv[1] == '--intro':
  INTRO=True
  del sys.argv[1]
filename = sys.argv[1]
nfs = sys.argv[2:]

# The labels/colors we'll use
def get_color_label_marker(nf):
  if nf == 'ada' or nf == 'ada-flexible':
    return ('#70B050', 'Ada', 'P') # P == filled plus
  if nf == 'ada-const':
    return ('#70B050', 'Ada, static output count', 'P')

  if nf == 'c-clang' or nf == 'c-flexible-clang':
    return ('#F08030', 'C', '^')
  if nf == 'c':
    return ('#BC6425', 'C, GCC', '>')
  if nf == 'c-const-clang':
    return ('#EF0731', 'C, static output count', '<')
  if nf == 'c-flexible' or nf == 'c-const':
    raise "unused"

  if nf == 'csharp' or nf == 'csharp-flexible':
    name = 'Extended C#' if INTRO else 'C#'
    return ('#28477E', name, 'X')
  if nf == 'csharp-noextensions':
    return ('#28477E', 'C# without extensions', 'X')

  if nf == 'rust' or nf == 'rust-flexible':
    name = 'Extended Rust' if INTRO else 'Rust'
    return ('#7D31ED', name, '.')
  if nf == 'rust-const':
    return ('#7D31ED', 'Rust, static output count', '.')


numbers = {}
all_vals = []
max_tput = 0
lats_comp = []
for nf in nfs:
  # Get the folder with NF data
  nf_folder = './results/' + nf
  # Parse the latencies, sorted
  lats_folder = pathlib.Path(nf_folder, 'latencies')
  lats = [(float(lat_file.name) / 1000, [float(l) / 1000.0 for l in lat_file.read_text().splitlines()]) for lat_file in lats_folder.glob('*')]
  lats = sorted(lats, key=lambda t: t[0])
  # Parse the throughput
  tput_file = pathlib.Path(nf_folder, 'throughput')
  tput = float(tput_file.read_text()) if tput_file.exists() else math.inf
  # Get the 5% and 95% latencies for the shaded areas, and the median latency for the bar
  def percentile(list, n):
    size = len(list)
    return sorted(list)[int(math.ceil((size * n) / 100)) - 1]
  def lats_at_perc(lats, perc):
    return [(t, percentile(ls, perc)) for (t, ls) in lats]
  lats_5 = lats_at_perc(lats, 5)
  lats_95 = lats_at_perc(lats, 95)
  lats_median = lats_at_perc(lats, 50)
  # Record all that
  numbers[nf] = (lats_5, lats_95, lats_median, tput)

for nf, val in numbers.items():
  (lats_5, lats_95, lats_med, _) = val
  x = [t for (t, l) in lats_med]
  y_5 = [l for (t, l) in lats_5]
  y_95 = [l for (t, l) in lats_95]
  y_med = [l for (t, l) in lats_med]
  (color, label, marker) = get_color_label_marker(nf)
  plt.plot(x, y_med, color=color, alpha=0.4, linestyle='solid')
  plt.fill_between(x, y_5, y_med, color=color, alpha=0.15)
  plt.fill_between(x, y_med, y_95, color=color, alpha=0.15)
  plt.scatter(x, y_med, color=color, marker=marker, s=60, label=label)
# Configure axes
plt.xlim(0, 0.2 + max(tput for (_, _, _, tput) in numbers.values()) / 1000.0) # just a little bit of margin to not hide the right side of the markers
plt.ylim(0, YLIM)
plt.xlabel('Throughput (Gb/s)')
plt.ylabel('Median latency (\u03BCs)')
plt.legend(loc='upper left', handletextpad=0.3, borderaxespad=0.08, edgecolor='white', frameon=False)
# Output
plot_dir = './plots/'
os.makedirs(plot_dir, exist_ok=True)
plt.savefig(plot_dir + filename + FILETYPE, bbox_inches='tight', pad_inches=0.025)
print("Done! Plot saved to plots/" + filename + FILETYPE)
