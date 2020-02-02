#!/usr/bin/python3

from common import *
import glob
import pathlib
import os
import sys

this_dir = os.path.dirname(os.path.realpath(__file__))

if len(sys.argv) != 4:
  print('[ERROR] Please provide 3 arguments: kind, NF, latency percentile')
  sys.exit(1)

kind = sys.argv[1]
nf = sys.argv[2]
perc = int(sys.argv[3])
perc_str = str(perc) + 'th percentile'
if perc == 50:
  perc_str = 'Median'

numbers = {}
for key_folder in [f for f in sorted(glob.glob(get_output_folder(kind, nf) + '/*')) if os.path.isdir(f)]:
  key = os.path.basename(key_folder)
  params = {}
  for param_folder in glob.glob(key_folder + '/*'):
    param = int(os.path.basename(param_folder))
    latencies = [(float(latf.name), int(percentile([int(l) for l in latf.read_text().splitlines()], perc))) for latf in pathlib.Path(param_folder, 'latencies').glob('*')]
    params[param] = sorted(latencies, key=lambda t: t[0])
  numbers[key] = dict(sorted(params.items()))

plt, ax = get_pyplot_ax(get_title(kind, nf))

for key, params in numbers.items():
  color = get_color(key)
  for param, latencies in params.items():
    x = [t for (t, l) in latencies]
    y = [l for (t, l) in latencies]
    # We want opaque dots with non-opaque lines, 'plot' doesn't seem to support that scenario alone
    ax.plot(x, y, color=color, alpha=0.3, linestyle='dashed')
    ax.scatter(x, y, color=color) #, label=key)

ax.set_xlim(left=0)
ax.set_ylim(bottom=0)
plt.xlabel('Throughput (Mbps)')
plt.ylabel(perc_str + ' latency (ns)')
#plt.legend(loc='upper left', handletextpad=0.3)

plt.savefig(get_output_folder(kind, nf) + '/full-' + str(perc) + '.svg', bbox_inches='tight')
