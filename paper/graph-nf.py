#!/usr/bin/python3

import csv
import os
import sys

this_dir = os.path.dirname(os.path.realpath(__file__))

if len(sys.argv) != 2: # script itself + 1 arg
  print('[ERROR] Please provide 1 arguments: the CSV filename to graph')
  sys.exit(1)

csv_file_name = os.path.basename(sys.argv[1])
csv_file_path = os.path.realpath(sys.argv[1])

values = {}
with open(csv_file_path, 'r', newline='') as csv_file:
  reader = csv.DictReader(csv_file)
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
  if key == 'original, batching':
    color = 'goldenrod'
  elif key == 'original':
    color = 'gold'
  elif 'shim' in key:
    color = 'blue'
    if 'simple' in key:
      color = 'turquoise'
  elif 'custom' in key:
    color = 'red'
    if 'simple' in key:
      color = 'magenta'

  if 'LTO' not in key:
    color = 'light ' + color

  x = [float(r['Throughput']) for r in value]
  y = [float(r['Latency-99th']) for r in value]
  # We want opaque dots with non-opaque lines, 'plot' doesn't seem to support that scenario alone
  ax.plot(x, y, color='xkcd:' + color, alpha=0.3, linestyle='dashed')
  ax.scatter(x, y, color='xkcd:' + color, label=key)

title_parts = csv_file_name.replace('.csv', '').split('-')
title = title_parts[0].title()
nf = title_parts[1]
if nf == 'nop':
  title += ' No-op'
elif nf == 'nat':
  title += ' NAT'
elif nf == 'bridge':
  title += ' Bridge'
elif nf == 'policer':
  title += ' Policer'
elif nf == 'fw':
  title += ' Firewall'
else:
  title += ' ' + nf

fig.suptitle(title, y=0.85, x=0.52) # put the title inside the plot to save space
plt.axis([0, 14000, 0, 30000])
plt.xlabel('Max throughput with <0.1% loss (Mbps)')
plt.ylabel('99th percentile latency (ns)')
plt.legend(loc='upper left', handletextpad=0.3)

plt.savefig(os.path.splitext(csv_file_name)[0] + '.pdf', bbox_inches='tight')
