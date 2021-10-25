#!/usr/bin/python3
from distutils.dir_util import copy_tree
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

def add_suffix(file_or_folder, suffix):
  os.rename(file_or_folder, file_or_folder + suffix)

def move_into(src, dst):
  if os.path.isdir(src):
    os.makedirs(dst, exist_ok=True)
    copy_tree(src, dst + '/')
  else:
    os.rename(src, dst + '/' + os.path.basename(src))

def remove(file_or_folder):
  if not os.path.exists(file_or_folder):
    return # ok, it's not there
  if os.path.isdir(file_or_folder):
    shutil.rmtree(file_or_folder)
  else:
    os.remove(file_or_folder)

# --- per-NF parameters ---

def get_cflags(nf, env):
  result = []
  result.append('-flto') # LTO
  result.append('-s') # strip
  return result

def get_benchflags(nf, env):
  return ['standard']

def get_layer(nf, env):
  return 2


# --- benchmarking ---

def bench(path, name, extra_env):
  print('[ !!! ] Benchmarking', name, 'in', path)
  out_folder = 'results/' + name + '/'

  # Just in case...
  subprocess.call(['sh', '-c', 'sudo rm -rf /dev/hugepages/*'])

  env = dict(os.environ)
  env.update(extra_env)
  env['TN_CFLAGS'] = env.get('TN_CFLAGS', '') + ' ' +  " ".join(get_cflags(None, env))

  benchflags = get_benchflags(None, env) + [str(get_layer(None, env))]

  while True: # bench.sh can fail for spurious reasons, e.g. random DNS failures during SSH login
    result = subprocess.run(['sh', 'bench.sh', path] + benchflags, cwd=BENCH_PATH, env=env).returncode
    if result == 0:
      break
    else:
      time.sleep(60)

  remove(out_folder + '/latencies') # don't keep old latencies around
  move_into(BENCH_RESULTS_PATH, out_folder)


cpu_low_power()
#bench('../c', 'C', {})
#bench('../c', 'C, dangerous', {'TN_CFLAGS': '-DDANGEROUS'})
#bench('../csharp', 'C#, JIT', {'CSHARP_MODE': 'safe'})
#bench('../csharp', 'C# extended, JIT', {'CSHARP_MODE': 'extended'})
#bench('../csharp', 'C#, AOT', {'CSHARP_MODE': 'safe', 'CSHARP_AOT': 'y'})
#bench('../csharp', 'C# extended, AOT', {'CSHARP_MODE': 'extended', 'CSHARP_AOT': 'y'})
bench('../rust', 'Rust', {})
#bench('../ada', 'Ada', {})
cpu_full_power()
