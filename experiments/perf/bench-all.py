#!/usr/bin/env python3

import os
import shutil
import subprocess
import sys
import time

THIS_DIR = os.path.dirname(os.path.realpath(__file__))

BENCH_PATH = THIS_DIR + '/../../benchmarking/'
BENCH_RESULTS_PATH = BENCH_PATH + '/results'
BENCH_RESULT_TPUT_PATH = BENCH_RESULTS_PATH + '/throughput'
BENCH_RESULT_LATS_PATH = BENCH_RESULTS_PATH + '/latencies'


# --- CPU throttling ---
BENCH_CPU = None
with open(THIS_DIR + '/../../benchmarking/config') as file:
  for line in file:
    if 'DUT_CPUS' in line:
      BENCH_CPU=line.split('=')[1].split(',')[0].strip()
      break
if BENCH_CPU is None:
  print("Could not find DUT CPUs in config...")
  sys.exit(1)
BENCH_CPU_CORES = None
with open('/sys/devices/system/cpu/cpu' + BENCH_CPU + '/topology/core_siblings_list') as file:
  BENCH_CPU_CORES = file.read().strip()

def cpu_full_power():
  subprocess.check_call(["sudo", "cpupower", "-c", BENCH_CPU_CORES, "frequency-set", "-f", "99GHz"], stdout=subprocess.DEVNULL)

def cpu_low_power():
  subprocess.check_call(["sudo", "cpupower", "-c", BENCH_CPU_CORES, "frequency-set", "-f", "1.5GHz"], stdout=subprocess.DEVNULL)


# --- utility ---
def move_into(src, dst):
  if os.path.isdir(src):
    os.makedirs(dst, exist_ok=True)
    shutil.copytree(src, dst + '/', dirs_exist_ok=True)
  else:
    os.rename(src, dst + '/' + os.path.basename(src))

def remove(file_or_folder):
  if not os.path.exists(file_or_folder):
    return # ok, it's not there
  if os.path.isdir(file_or_folder):
    shutil.rmtree(file_or_folder)
  else:
    os.remove(file_or_folder)

# --- benchmarking ---
def bench(path, name, extra_env):
  print('[ !!! ] Benchmarking', name, 'in', path)
  out_folder = 'results/' + name + '/'

  # Just in case...
  subprocess.call(['sh', '-c', 'sudo rm -rf /dev/hugepages/*'])

  env = dict(os.environ)
  env.update(extra_env)

  while True: # bench.sh can fail for spurious reasons, e.g. random DNS failures during SSH login
    result = subprocess.run(['sh', 'bench.sh', path, 'standard', '2'], cwd=BENCH_PATH, env=env).returncode
    if result == 0:
      break
    else:
      time.sleep(60)

  remove(out_folder + '/latencies') # don't keep old latencies around
  move_into(BENCH_RESULTS_PATH, out_folder)



cpu_low_power()
bench('../c', 'c', {})
bench('../c', 'c-clang', {'TN_CC': 'clang'})
bench('../c', 'c-const', {'TN_MODE': '1'})
bench('../c', 'c-const-clang', {'TN_MODE': '1', 'TN_CC': 'clang'})
bench('../c', 'c-queues', {'TN_MODE': '2'})
bench('../c', 'c-queues-clang', {'TN_MODE': '2', 'TN_CC': 'clang'})
bench('../csharp', 'csharp-safe', {'TN_MODE': '3', 'TN_CSHARP_AOT': 'y'})
bench('../csharp', 'csharp', {'TN_CSHARP_AOT': 'y'})
bench('../csharp', 'csharp-queues', {'TN_MODE': '2', 'TN_CSHARP_AOT': 'y'})
bench('../rust', 'rust', {})
bench('../rust', 'rust-const', {'TN_MODE': '1'})
bench('../rust', 'rust-queues', {'TN_MODE': '2'})
bench('../ada', 'ada', {})
bench('../ada', 'ada-const', {'TN_MODE': '1'})
bench('../ada', 'ada-queues', {'TN_MODE': '2'})
cpu_full_power()
