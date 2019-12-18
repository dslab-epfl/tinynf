#!/usr/bin/python3

from common import *
import csv
import os
import sys

this_dir = os.path.dirname(os.path.realpath(__file__))

if len(sys.argv) != 3: # script itself + 2 args
  print('[ERROR] Please provide 2 arguments: the kind and NF')
  sys.exit(1)

kind = sys.argv[1]
nf = sys.argv[2]
csv_file_path = get_output_filename(kind, nf, 'data.csv')

values = {}
with open(csv_file_path, 'r', newline='') as csv_file:
  reader = csv.DictReader(csv_file, skipinitialspace=True)
  for row in reader:
    key = row['Key']
    if key not in values:
      values[key] = []
    values[key].append(row) # we assume rows are sorted by period

import matplotlib as mpl
mpl.use('Agg') # avoid the need for an X server
import matplotlib.pyplot as plt

fig = plt.figure()
ax = fig.add_subplot(1, 1, 1)

# Remove top and right spines
ax.spines['top'].set_visible(False)
ax.spines['right'].set_visible(False)

for key, value in values.items():
  color = get_color(key)
  x = [float(r['Throughput']) for r in value]
  y = [float(r['Latency-99th']) for r in value]
  # We want opaque dots with non-opaque lines, 'plot' doesn't seem to support that scenario alone
  ax.plot(x, y, color=color, alpha=0.3, linestyle='dashed')
  ax.scatter(x, y, color=color, label=key)

title = get_title(kind, nf)

fig.suptitle(title, y=0.85, x=0.52) # put the title inside the plot to save space
ax.set_xlim(left=0)
ax.set_ylim(bottom=0)
plt.xlabel('Max throughput with <0.1% loss (Mbps)')
plt.ylabel('99th percentile latency (ns)')
plt.legend(loc='upper left', handletextpad=0.3)

plt.savefig(get_output_filename(kind, nf, 'data.pdf'), bbox_inches='tight')
