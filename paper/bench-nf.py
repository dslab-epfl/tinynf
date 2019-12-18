#!/usr/bin/python3
# I rewrote this in Python from a Bash script. So I kept the naming convention of ALL_CAPS even though it's ugly. Oh well.

import glob
import os
import shutil
import subprocess
import sys
import time

THIS_DIR = os.path.dirname(os.path.realpath(__file__))
BENCH_DIR = THIS_DIR + '/../benchmarking/'

if len(sys.argv) != 3: # script itself + 2 args
  print('[ERROR] Please provide 2 arguments: <NF directory> <NF (e.g. nop, nat, bridge...)>')
  sys.exit(1)

NF_DIR_BASE = os.path.realpath(sys.argv[1])
NF_DIR_NAME = os.path.basename(NF_DIR_BASE)
NF = sys.argv[2]

OUTPUT_DIR = THIS_DIR + '/results/' + NF_DIR_NAME + '/' + NF
shutil.rmtree(OUTPUT_DIR, ignore_errors=True)
OUTPUT_LATENCIES_DIR_BASE = OUTPUT_DIR + '/latencies'

if NF == 'bridge':
  LAYER = '2' # MAC
elif NF == 'pol':
  LAYER = '3' # Policer is by IP
else:
  LAYER = '4'

# Vigor-specific
# Expiration time default is 10us which is nothing; use 120Mus (i.e. 120s) instead
os.environ['EXPIRATION_TIME'] = '120000000'
# Bridge needs double the standard capacity since it stores both input and output flows
if NF == 'bridge':
  os.environ['CAPACITY'] = '131072'
# Policer needs large maximums so as to not really police, since we measure throughput
elif NF == 'pol':
  os.environ['POLICER_BURST'] = '10000000000'
  os.environ['POLICER_RATE'] = '10000000000'

NF_KIND_CHOICES = ['custom', 'dpdk-shim', 'dpdk']

RESULTS = {}
COLORS = {}
for NF_KIND in NF_KIND_CHOICES:
  PARAM_CHOICES = ['2', '4', '8', '16', '32', '64', '128', '256', '512']
  CUSTOM_ENV = {}
  if NF_KIND == 'custom' or NF_KIND == 'dpdk-shim':
    # Necessary if DPDK has been used before and didn't exit cleanly (call sh to have it expand the *)
    subprocess.call(['sh', '-c', 'sudo rm -rf /dev/hugepages/*'])

    LTO_CHOICES = [True, False]
    ONEWAY_CHOICES = [True, False]
    if NF_KIND == 'custom':
      NF_DIR = NF_DIR_BASE
    else:
      NF_DIR = NF_DIR_BASE + '/with-dpdk'
      CUSTOM_ENV = { 'RTE_SDK': THIS_DIR + '/../shims/dpdk', 'RTE_TARGET': '.' }
  else:
    PARAM_CHOICES = ['1'] + PARAM_CHOICES
    LTO_CHOICES = [False]
    ONEWAY_CHOICES = [False]
    NF_DIR = NF_DIR_BASE + '/with-dpdk'

  # Bridge can't do one-way, by definition it may need to flood
  # (even with only 2 devices, enabling one-way would be misleading)
  if NF == 'bridge':
    ONEWAY_CHOICES = [False]

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

      for PARAM in PARAM_CHOICES:
        if NF_KIND == 'dpdk':
          PARAM_FLAG = ''
          CUSTOM_ENV['TN_BATCH_SIZE'] = PARAM
        else:
          PARAM_FLAG = '-DIXGBE_PIPE_SCHEDULING_PERIOD=' + PARAM

        if NF_KIND == 'dpdk':
          KEY = 'original'
          COLORS[KEY] = 'gold'
        elif NF_KIND == 'dpdk-shim':
          KEY = 'shim'
          COLORS[KEY] = 'blue'
          if ONEWAY:
            KEY += ', simple'
            COLORS[KEY] = 'cyan'
        else:
          KEY = 'custom'
          COLORS[KEY] = 'red'
          if ONEWAY:
            KEY += ', simple'
            COLORS[KEY] = 'magenta'
        if LTO:
          NEWKEY = KEY + ', LTO'
          COLORS[NEWKEY] = 'dark' + COLORS[KEY]
          KEY = NEWKEY

        # Bench kind is the only thing guaranteed to not need a recompilation (as long as the NF Makefile is smart), so let's do it in the inner loop
        VALUES = []
        for BENCH_KIND in ['throughput', 'latency']:
          ENV = dict(os.environ)
          ENV['TN_NF'] = NF
          ENV['TN_LDFLAGS'] = LTO_FLAG
          ENV['TN_CFLAGS'] = LTO_FLAG + ' ' + ONEWAY_FLAG + ' ' + PARAM_FLAG
          ENV.update(CUSTOM_ENV)

          # can fail for spurious reasons, e.g. random DNS failures
          while True:
            print('[!!!] Benchmarking "' + KEY + '" for ' + BENCH_KIND + ' (param: ' + str(PARAM) + ') ...')
            RESULT = subprocess.run(['sh', 'bench.sh', NF_DIR, BENCH_KIND, LAYER], cwd=BENCH_DIR, env=ENV).returncode
            if RESULT == 0:
              break
            else:
              time.sleep(60)

          with open(BENCH_DIR + '/bench.result', mode='r') as FILE:
            VALUES.append(FILE.read().strip())

          if BENCH_KIND == 'latency':
            DIR = OUTPUT_LATENCIES_DIR_BASE + '/' + KEY
            os.makedirs(DIR, exist_ok=True)
            os.rename(BENCH_DIR + '/bench-detailed.result', DIR + '/' + PARAM)

        if KEY not in RESULTS:
          RESULTS[KEY] = {}

        RESULTS[KEY][PARAM] = VALUES

os.makedirs(OUTPUT_DIR, exist_ok=True)
with open(OUTPUT_DIR + '/data.csv', 'w') as FILE:
  FILE.write('Key, Param, Throughput, Latency-Min, Latency-Max, Latency-Median, Latency-Stdev, Latency-99th\n')
  for (KEY, ITEMS) in RESULTS.items():
    for (PARAM, VALUES) in ITEMS.items():
      FILE.write('"' + KEY + '", ' + PARAM + ', ' + ', '.join(VALUES) + '\n')
