#!/usr/bin/python3
# I rewrote this in Python from a Bash script. So I kept the naming convention of ALL_CAPS even though it's ugly. Oh well.

from common import *
from distutils.dir_util import copy_tree
import glob
import os
import subprocess
import sys
import time

THIS_DIR = os.path.dirname(os.path.realpath(__file__))
BENCH_DIR = THIS_DIR + '/../benchmarking/'

if len(sys.argv) < 3: # script itself + 2 args
  print('[ERROR] Please provide 2 arguments: <NF directory> <NF (e.g. nop, nat, bridge...)>')
  sys.exit(1)

NF_DIR_BASE = os.path.realpath(sys.argv[1])
NF_DIR_NAME = os.path.basename(NF_DIR_BASE)
NF = sys.argv[2]

if len(sys.argv) == 4:
  if sys.argv[3] == 'single':
    NF_KIND_CHOICES = ['custom', 'dpdk']
    BENCH_KIND = ['-l', '1000', 'standard-single']
    FILE_SUFFIX = '-single'
  else:
    print('[ERROR] Unknown bench kind')
    sys.exit(1)
else:
  NF_KIND_CHOICES = ['custom', 'dpdk-shim', 'dpdk']
  BENCH_KIND = ['standard']
  FILE_SUFFIX = ''

OUTPUT_DIR = get_output_folder(NF_DIR_NAME, NF)

if NF == 'bridge':
  LAYER = '2' # MAC
elif NF == 'pol':
  LAYER = '3' # Policer is by IP
else:
  LAYER = '4'

# Vigor-specific
# Expiration time default is 10us which is nothing
os.environ['EXPIRATION_TIME'] = '4000000'
# Bridge needs double the standard capacity since it stores both input and output flows
if NF == 'bridge':
  os.environ['CAPACITY'] = '131072'
# Policer needs large maximums so as to not really police, since we measure throughput
elif NF == 'pol':
  os.environ['POLICER_BURST'] = '10000000000'
  os.environ['POLICER_RATE'] = '10000000000'

RESULTS = {}
for NF_KIND in NF_KIND_CHOICES:
  CUSTOM_ENV = {}
  if NF_KIND == 'custom' or NF_KIND == 'dpdk-shim':
    # Necessary if DPDK has been used before and didn't exit cleanly (call sh to have it expand the *)
    subprocess.call(['sh', '-c', 'sudo rm -rf /dev/hugepages/*'])

    BATCH_CHOICES = ['1']
    LTO = True
    ONEWAY_CHOICES = [True] # [True, False]
    if NF_KIND == 'custom':
      NF_DIR = NF_DIR_BASE
    else:
      NF_DIR = NF_DIR_BASE + '/with-dpdk'
      CUSTOM_ENV = { 'RTE_SDK': THIS_DIR + '/../shims/dpdk', 'RTE_TARGET': '.' }
  else:
    BATCH_CHOICES = ['1', '64']
    LTO = False
    ONEWAY_CHOICES = [False]
    NF_DIR = NF_DIR_BASE + '/with-dpdk'

  # Bridge can't do one-way, by definition it may need to flood
  # (even with only 2 devices, enabling one-way would be misleading)
  if NF == 'bridge':
    ONEWAY_CHOICES = [False]

  if LTO:
    LTO_FLAG = '-flto'
  else:
    LTO_FLAG = ''

  for ONEWAY in ONEWAY_CHOICES:
    if ONEWAY:
      ONEWAY_FLAG = '-DASSUME_ONE_WAY -DIXGBE_PIPE_MAX_SENDS=1'
    else:
      ONEWAY_FLAG = '-DIXGBE_PIPE_MAX_SENDS=2'

    for BATCH in BATCH_CHOICES:
      if NF_KIND == 'dpdk':
        CUSTOM_ENV['TN_BATCH_SIZE'] = BATCH

      if NF_KIND == 'dpdk':
        KEY = 'original'
      elif NF_KIND == 'dpdk-shim':
        KEY = 'shim'
        if ONEWAY:
          KEY += ', simple'
      else:
        KEY = 'custom'
        if ONEWAY:
          KEY += ', simple'

      ENV = dict(os.environ)
      ENV['TN_NF'] = NF
      ENV['TN_LDFLAGS'] = LTO_FLAG
      ENV['TN_CFLAGS'] = LTO_FLAG + ' ' + ONEWAY_FLAG
      ENV.update(CUSTOM_ENV)

      # can fail for spurious reasons, e.g. random DNS failures
      while True:
        print('[!!!] Benchmarking "' + KEY + '", batch: ' + str(BATCH) + ' ...')
        RESULT = subprocess.run(['sh', 'bench.sh', NF_DIR] + BENCH_KIND + [LAYER], cwd=BENCH_DIR, env=ENV).returncode
        if RESULT == 0:
          break
        else:
          time.sleep(60)

      BENCH_RESULTS_PATH = BENCH_DIR + '/results'
      TPUT_FILE_PATH = BENCH_RESULTS_PATH + '/throughput'
      LAT_FOLDER_PATH = BENCH_RESULTS_PATH + '/latencies'

      os.rename(TPUT_FILE_PATH, TPUT_FILE_PATH + FILE_SUFFIX)
      os.rename(LAT_FOLDER_PATH, LAT_FOLDER_PATH + FILE_SUFFIX)

      DIR = OUTPUT_DIR + '/' + KEY + '/' + str(BATCH)
      os.makedirs(DIR, exist_ok=True)
      copy_tree(BENCH_RESULTS_PATH, DIR)
