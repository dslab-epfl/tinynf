#!/usr/bin/python3

# I rewrote this in Python from a Bash script. So I kept the naming convention of ALL_CAPS even though it's ugly. Oh well.

import csv
import glob
import os
import subprocess
import sys

THIS_DIR = os.path.dirname(os.path.realpath(__file__))
BENCH_DIR = THIS_DIR + '/../benchmarking/'

if len(sys.argv) != 3: # script itself + 2 args
  print('[ERROR] Please provide 2 arguments: <NF directory> <NF (e.g. nop, nat, bridge...)>')
  sys.exit(1)

NF_DIR_BASE = os.path.realpath(sys.argv[1])
NF_DIR_NAME = os.path.basename(NF_DIR_BASE)
NF = sys.argv[2]

# Necessary if DPDK has been used before and didn't exit cleanly (call sh to have it expand the *)
subprocess.call(['sh', '-c', 'sudo rm -rf /dev/hugepages/*'])

# Pick the layer
if NF == 'bridge':
  LAYER = '2'
elif NF == 'pol':
  LAYER = '3'
else:
  LAYER = '4'

# Vigor-specific
# Bridge needs double the standard capacity since it stores both input and output flows
if NF == 'bridge':
  os.environ['CAPACITY'] = '131072'
# Policer needs large maximums so as to not really police, since we measure throughput
elif NF == 'pol':
  os.environ['POLICER_BURST'] = '10000000000'
  os.environ['POLICER_RATE'] = '10000000000'


NF_KIND_CHOICES = ['custom', 'dpdk-shim', 'dpdk']
if NF_DIR_NAME == 'click': # only Click supports this
  NF_KIND_CHOICES.append('dpdk-batch')

RESULTS = {}
for NF_KIND in NF_KIND_CHOICES:
  if NF_KIND == 'custom':
    LTO_CHOICES = [True, False]
    PERIOD_CHOICES = ['2', '4', '8', '16', '32', '64', '128', '256', '512']
    ONEWAY_CHOICES = [True] # no reason not to since we're doing custom anyway
    NF_DIR = NF_DIR_BASE
    CUSTOM_ENV = {}
  elif NF_KIND == 'dpdk-shim':
    LTO_CHOICES = [True, False]
    PERIOD_CHOICES = ['2', '4', '8', '16', '32', '64', '128', '256', '512']
    ONEWAY_CHOICES = [True, False]
    NF_DIR = NF_DIR_BASE + '/with-dpdk'
    CUSTOM_ENV = { 'RTE_SDK': THIS_DIR + '/../shims/dpdk', 'RTE_TARGET': '.' }
  else:
    LTO_CHOICES = [False]
    PERIOD_CHOICES = ['']
    ONEWAY_CHOICES = [False]
    NF_DIR = NF_DIR_BASE + '/with-dpdk'
    if NF_KIND == 'dpdk-batch':
      CUSTOM_ENV = {'TN_BATCH_SIZE': '32'}
    else:
      CUSTOM_ENV = {}

  # Bridge can't do one-way, by definition it may need to flood
  # (even with only 2 devices, enabling one-way would be misleading)
  if NF == 'bridge':
    ONEWAY_CHOICES = ['false']

  for ONEWAY in ONEWAY_CHOICES:
    if ONEWAY:
      ONEWAY_FLAG = '-DASSUME_ONE_WAY -DIXGBE_PIPE_MAX_SENDS=1'
    else:
      ONEWAY_FLAG = '-DIXGBE_PIPE_MAX_SENDS=2'

    for LTO in LTO_CHOICES:
      if LTO:
        LTO_FLAG = '-flto'
      else:
        LTO_FLAG = ''

      for PERIOD in PERIOD_CHOICES:
        if PERIOD == '':
          PERIOD_FLAG = ''
        else:
          PERIOD_FLAG = '-DIXGBE_PIPE_SCHEDULING_PERIOD=' + PERIOD

        # Bench kind is the only thing guaranteed to not need a recompilation (as long as the NF Makefile is smart), so let's do it in the inner loop
        VALUES = []
        for BENCH_KIND in ['throughput', 'latency']:
          ENV = dict(os.environ)
          ENV['TN_NF'] = NF
          ENV['TN_LDFLAGS'] = LTO_FLAG
          ENV['TN_CFLAGS'] = LTO_FLAG + ' ' + ONEWAY_FLAG + ' ' + PERIOD_FLAG
          ENV.update(CUSTOM_ENV)
          subprocess.run(['sh', 'bench.sh', NF_DIR, BENCH_KIND, LAYER], cwd=BENCH_DIR, env=ENV)

          with open(BENCH_DIR + '/bench.results', newline='') as FILE:
            CSV = list(csv.reader(FILE))
            VALUES.append(CSV[1][0].strip())
            if BENCH_KIND == 'latency':
              VALUES.append(CSV[1][1].strip())

        if NF_KIND == 'dpdk':
          KEY = 'original'
        elif NF_KIND == 'dpdk-batch':
          KEY = 'original with batching'
        elif NF_KIND == 'dpdk-shim':
          KEY = 'shim'
          if ONEWAY:
            KEY += ', simple'
        else:
          KEY = 'custom'

        if LTO:
          KEY += ', LTO'

        if KEY not in RESULTS:
          RESULTS[KEY] = {}

        RESULTS[KEY][PERIOD] = VALUES

FILE_PREFIX = THIS_DIR + '/' + NF_DIR_NAME + '-' + NF

with open(FILE_PREFIX + '.csv', 'w', newline='') as FILE:
  CSV = csv.writer(FILE)
  CSV.writerow(['Key', 'Period', 'Throughput', 'Latency-median', 'Latency-stdev'])
  for (KEY, ITEMS) in RESULTS.items():
    for (PERIOD, VALUES) in ITEMS.items():
      CSV.writerow([KEY, PERIOD] + VALUES)

# and now for the reason this is Python in the first place...
import matplotlib as mpl
mpl.use('Agg') # this doesn't need an X server
import matplotlib.pyplot as plt

fig = plt.figure()
ax = fig.add_subplot(1, 1, 1)

for (INDEX, (KEY, ITEMS)) in enumerate(RESULTS.items()):
  line, caps, bars = ax.errorbar(x=[int(t) for (t, lm, ls) in ITEMS.values()], y=[int(lm) for (t, lm, ls) in ITEMS.values()], yerr=[int(float(ls)) for (t, lm, ls) in ITEMS.values()], label=KEY, fmt='o')
  line.set_linestyle((INDEX % 4, (4, 2))) # dashes, with an offset to avoid colliding all lines
  [bar.set_alpha(0.3) for bar in bars]

PLOT_TITLE = NF_DIR_NAME.title()
if NF == 'nop':
  PLOT_TITLE += ' No-op'
elif NF == 'nat':
  PLOT_TITLE += ' NAT'
elif NF == 'bridge':
  PLOT_TITLE += ' Bridge'
elif NF == 'policer':
  PLOT_TITLE += ' Policer'
elif NF == 'fw':
  PLOT_TITLE += ' Firewall'
else:
  PLOT_TITLE += ' ' + NF

fig.suptitle(PLOT_TITLE, y=0.5) # reduce y from its default of ~1 to leave less blank space at the top
plt.axis([0, 15000, 0, 20000])
plt.xlabel('Throughput (Mbps)')
plt.ylabel('Latency (ns)')
plt.legend(loc='upper left')

plt.savefig(FILE_PREFIX + '.pdf', bbox_inches='tight')
