#!/usr/bin/python3

# I rewrote this in Python from a Bash script. So I kept the naming convention of ALL_CAPS even though it's ugly. Oh well.

import csv
import glob
import os
import subprocess
import sys

THIS_DIR = os.path.dirname(os.path.realpath(__file__))
BENCH_DIR = THIS_DIR + '/../benchmarking/'

if len(sys.argv) != 4: # script itself + 3 args
  print('[ERROR] Please provide 3 arguments: <NF directory> <kind: custom/dpdk-shim/dpdk> <NF>')
  sys.exit(1)

NF_DIR = os.path.realpath(sys.argv[1])
NF_DIR_CLEAN = NF_DIR.strip('/').replace('/', '_') # remove leading/trailing slash, replace / by _

NF_KIND = sys.argv[2]
if NF_KIND == 'custom':
    LTO_CHOICES = [True, False]
    PERIOD_CHOICES = ['2', '4', '8', '16', '32', '64', '128', '256', '512', '1024']
    ONEWAY_CHOICES = [True] # no reason not to since we're doing custom anyway
elif NF_KIND == 'dpdk-shim':
    LTO_CHOICES = [True, False]
    PERIOD_CHOICES = ['2', '4', '8', '16', '32', '64', '128', '256', '512', '1024']
    ONEWAY_CHOICES = [True, False]
    os.environ['RTE_SDK'] = THIS_DIR + '/../shims/dpdk'
    os.environ['RTE_TARGET'] = '.'
elif NF_KIND == 'dpdk':
    LTO_CHOICES = [False]
    PERIOD_CHOICES = ['']
    ONEWAY_CHOICES = [False]
else:
    print('[ERROR] Unknown kind')
    sys.exit(1)

NF = sys.argv[3]


# Necessary if DPDK has been used before and didn't exit cleanly
subprocess.call(['sudo', 'rm', '-rf', '/dev/hugepages/*'])

# Pick the layer
if NF == 'bridge':
  LAYER = '2'
elif NF == 'pol':
  LAYER = '3'
else:
  LAYER = '4'

# Bridge can't do one-way, by definition it may need to flood
# (even with only 2 devices, enabling one-way would be misleading)
if NF == 'bridge':
  ONEWAY_CHOICES = ['false']

# Vigor-specific
# Bridge needs double the standard capacity since it stores both input and output flows
if NF == 'bridge':
  os.environ['CAPACITY'] = '131072'
# Policer needs large maximums so as to not really police, since we measure throughput
elif NF == 'pol':
  os.environ['POLICER_BURST'] = '10000000000'
  os.environ['POLICER_RATE'] = '10000000000'


RESULTS = {}

for LTO in LTO_CHOICES:
  if LTO:
    LTO_FLAG = '-flto'
  else:
    LTO_FLAG = ''

  for ONEWAY in ONEWAY_CHOICES:
    if ONEWAY:
      ONEWAY_FLAG = '-DASSUME_ONE_WAY -DIXGBE_PIPE_MAX_SENDS=1'
    else:
      ONEWAY_FLAG = '-DIXGBE_PIPE_MAX_SENDS=2'

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
        subprocess.run(['sh', 'bench.sh', NF_DIR, BENCH_KIND, LAYER], cwd=BENCH_DIR, env=ENV)

        with open(BENCH_DIR + '/bench.results', newline='') as FILE:
          CSV = list(csv.reader(FILE))
          VALUES.append(CSV[1][0].strip())
          if BENCH_KIND == 'latency':
            VALUES.append(CSV[1][1].strip())

      if NF_KIND == 'dpdk':
        KEY = 'original'
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

FILE_PREFIX = THIS_DIR + '/' + NF_DIR_CLEAN + '--' + NF_KIND + '--' + NF

with open(FILE_PREFIX + '.csv', 'w', newline='') as FILE:
  CSV = csv.writer(FILE)
  CSV.writerow(['Key', 'Period', 'Throughput', 'Latency-median', 'Latency-stdev'])
  for (KEY, ITEMS) in RESULTS.items():
    for (PERIOD, VALUES) in ITEMS.items():
      CSV.writerow([KEY, PERIOD] + VALUES)
