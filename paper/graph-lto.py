#!/usr/bin/python3

from common import *
import glob
import itertools
import pathlib
import os
import sys

this_dir = os.path.dirname(os.path.realpath(__file__))

if len(sys.argv) != 4:
  print('[ERROR] Please provide 3 arguments: kind, latency percentile, latload')
  sys.exit(1)

kind = sys.argv[1]
nfs = ['nat', 'nop', 'bridge', 'fw', 'pol']
perc = int(sys.argv[2])
perc_str = str(perc) + 'th percentile'
if perc == 50:
  perc_str = 'Median'
latload = sys.argv[3]

tputsY = []
latsY = []
tputsN = []
latsN = []
for nf in nfs:
  cust = 'custom, simple'
  if nf == 'bridge': cust = 'custom'
  tputY = int(pathlib.Path(get_output_folder(kind, nf), cust, '1', 'throughput').read_text().strip())
  tputN = int(pathlib.Path(get_output_folder(kind, nf), cust + ', no-lto', '1', 'throughput').read_text().strip())
  latY = percentile([float(l) / 1000.0 for l in pathlib.Path(get_output_folder(kind, nf), cust, '1', 'latencies', latload).read_text().splitlines()], perc)
  latN = percentile([float(l) / 1000.0 for l in pathlib.Path(get_output_folder(kind, nf), cust + ', no-lto', '1', 'latencies', latload).read_text().splitlines()], perc)
  tputsY.append(tputY)
  tputsN.append(tputN)
  latsY.append(latY)
  latsN.append(latN)

import matplotlib as mpl
mpl.use('Agg') # avoid the need for an X server
import matplotlib.pyplot as plt
# Avoid margins for axes
plt.rcParams['axes.ymargin'] = 0
plt.rcParams['axes.xmargin'] = 0

fig, ax = plt.subplots(1, 1)
ax.set_ylim(bottom=0, top=max(max(tputsY), max(tputsN)))

x = list(range(len(nfs)))
width = 0.35 # inspired by https://matplotlib.org/3.1.1/gallery/lines_bars_and_markers/barchart.html

r1 = ax.bar([a - width/2 for a in x], tputsY, width, label='LTO', color='xkcd:dark lime green')
r2 = ax.bar([a + width/2 for a in x], tputsN, width, label='No LTO', color='xkcd:brick red')

# Remove top/right spines
ax.spines['top'].set_visible(False)
ax.spines['right'].set_visible(False)

def translate(nf):
  if nf == 'nop':
    return 'No-op'
  elif nf == 'nat':
    return 'NAT'
  elif nf == 'bridge':
    return 'Bridge'
  elif nf == 'pol':
    return 'Policer'
  elif nf == 'fw':
    return 'Firewall'
  return '???'

ax.set_ylabel('Throughput (Mbps)')
ax.set_xticks(x)
ax.set_xticklabels([translate(nf) for nf in nfs])
ax.legend()

plt.savefig('lto.svg', bbox_inches='tight', pad_inches=0.01)
