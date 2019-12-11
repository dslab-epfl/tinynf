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
values = [[int(l.strip()) for l in open(get_lat_dir(kind, nf, arg[0], arg[1]), 'r')] for arg in args]

plt, ax = get_pyplot_ax(get_title(kind, nf))
plot = ax.boxplot(values, whis='range', labels=keys, patch_artist=True)
for box, key in zip(plot['boxes'], keys):
  box.set_facecolor(get_color(key))

ax.set_ylim(bottom=0)
plt.ylabel('Latency (ns)')
plt.savefig(get_output_filename(kind, nf, 'latencies.pdf'), bbox_inches='tight')
