#!/usr/bin/python3
from distutils.dir_util import copy_tree
import os
import shutil
import subprocess
import time

THIS_DIR = os.path.dirname(os.path.realpath(__file__))

RTE_SDK = '/home/solal/dpdk' # TODO FIXME
RTE_TARGET = 'x86_64-native-linuxapp-gcc'
RTE_FAKE_SDK = THIS_DIR + '/../shims/dpdk'
RTE_FAKE_TARGET = '.'
BATCH_SIZE = '32'

BENCH_PATH = THIS_DIR + '/../benchmarking/'
BENCH_RESULTS_PATH = BENCH_PATH + '/results'
BENCH_RESULT_TPUT_PATH = BENCH_RESULTS_PATH + '/throughput'
BENCH_RESULT_LATS_PATH = BENCH_RESULTS_PATH + '/latencies'


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

def has_dpdk(env):
  return 'RTE_SDK' in env

# --- per-NF parameters ---

def get_key(nf, env):
  suffix = ''
  if has_dpdk(env):
    if env['RTE_TARGET'] == '.':
      suffix += '-shimmed'
    else:
      suffix += '-dpdk'
  if env.get('TN_BATCH_SIZE', '1') != '1':
    suffix += '-batched'
  return nf + suffix

def get_env(nf, env):
  result = {}
  result['TN_DEBUG'] = '0'
  result['TN_NF'] = nf
  # Expiration time default is 10us which is nothing
  result['EXPIRATION_TIME'] = '4000000'
  # Bridge needs flows in both directions
  if nf == 'bridge':
    result['CAPACITY'] = '131072'
  # Policer needs large maximums so as to not really police, since we measure throughput
  if nf == 'pol':
    result['POLICER_BURST'] = '1000000000000'
    result['POLICER_RATE'] = '1000000000000'
  if nf == 'lb':
    # Device from which the load balancer will receive packets (and not heartbeats)
    result['WAN_DEVICE'] = '0'
  return result

def get_benchflags(nf, env):
  if nf == 'lb':
    # LB needs reverse heatup to work
    return ['-r']
  return []

def get_cflags(nf, env):
  result = []
  if not has_dpdk(env) or env['RTE_TARGET'] == '.':
    result.append('-flto')
    result.append('-DIXGBE_AGENT_OUTPUTS_MAX=1')
    result.append('-DASSUME_ONE_WAY')
  return result

def get_layer(nf, env):
  if nf == 'nat' or nf == 'lb' or nf == 'fw':
    return 4
  if nf == 'pol':
    return 3
  return 2


# --- benchmarking ---

def bench_core(nf, nf_dir, benchflags, additional_env):
  # Just in case...
  subprocess.call(['sh', '-c', 'sudo rm -rf /dev/hugepages/*'])

  env = dict(os.environ)
  env.update(get_env(nf, env))
  env.update(additional_env)
  env['TN_CFLAGS'] = " ".join(get_cflags(nf, env))
  env['TN_LDFLAGS'] = env['TN_CFLAGS'] # TODO this should not be needed, fix makefiles

  benchflags = get_benchflags(nf, env) + benchflags + [str(get_layer(nf, env))]

  while True: # bench.sh can fail for spurious reasons, e.g. random DNS failures during SSH login
    result = subprocess.run(['sh', 'bench.sh', nf_dir] + benchflags, cwd=BENCH_PATH, env=env).returncode
    if result == 0:
      break
    else:
      time.sleep(60)

def bench_vigor(nf, env):
  print('[ !!! ] Benchmarking', nf, 'in the Vigor way')
  suffix = '/with-dpdk' if has_dpdk(env) else ''
  bench_core(nf, THIS_DIR + '/../baselines/vigor' + suffix, ['--acceptableloss=0.001', '--latencyload=1000', 'standard-single'], env)
  out_folder = 'results/vigor-' + get_key(nf, env)
  remove(out_folder + '/latencies-single') # don't keep old latencies around
  add_suffix(BENCH_RESULT_TPUT_PATH, '-single')
  add_suffix(BENCH_RESULT_LATS_PATH, '-single')
  move_into(BENCH_RESULTS_PATH, out_folder)

def bench(path, nf, kind, env):
  print('[ !!! ] Benchmarking', kind, nf, 'in', path)
  out_folder = 'results/' + kind + '-' + get_key(nf, env)
  bench_core(nf, THIS_DIR + '/../' + path, ['standard'], env)
  remove(out_folder + '/latencies') # don't keep old latencies around
  move_into(BENCH_RESULTS_PATH, out_folder)
  #bench_core(nf, THIS_DIR + '/../' + path, ['--acceptableloss=0', '--latencyload=-1', 'standard'], env)
  #add_suffix(BENCH_RESULT_TPUT_PATH, '-zeroloss')
  #move_into(BENCH_RESULT_TPUT_PATH + '-zeroloss', out_folder)


# Overall, because binding DPDK's igb_uio driver has a slight chance of hanging the machine for some reason,
# each step performs all non-DPDK stuff first then all DPDK stuff

# DPDK's testpmd no-op, batched or not, vs TinyNF no-op vs Ixy no-op (throughput, zero-loss throughput, detailed latency)
if 0:
  bench('code', 'nop', 'tinynf', {})
  bench('baselines/ixy', 'nop', 'ixy', {})
  bench('baselines/ixy', 'nop', 'ixy', {'TN_BATCH_SIZE': BATCH_SIZE})
  bench('baselines/dpdk', 'nop', 'dpdk', {'RTE_SDK': RTE_SDK, 'RTE_TARGET': RTE_TARGET})
  bench('baselines/dpdk', 'nop', 'dpdk', {'RTE_SDK': RTE_SDK, 'RTE_TARGET': RTE_TARGET, 'TN_BATCH_SIZE': BATCH_SIZE})

# VigPol with TinyNF vs TinyNF-DPDK-shim vs DPDK vs DPDK batched, and parallel versions of TinyNF, DPDK, DPDK batched
if 1:
  bench('baselines/vigor', 'pol', 'vigor', {})
  bench('baselines/vigor/with-dpdk', 'pol', 'vigor', {'RTE_SDK': RTE_FAKE_SDK, 'RTE_TARGET': RTE_FAKE_TARGET})
  bench('baselines/parallel-policer/tinynf', 'pol', 'tinynf-parallel', {})
  bench('baselines/vigor/with-dpdk', 'pol', 'vigor', {'RTE_SDK': RTE_SDK, 'RTE_TARGET': RTE_TARGET})
  bench('baselines/vigor/with-dpdk', 'pol', 'vigor', {'RTE_SDK': RTE_SDK, 'RTE_TARGET': RTE_TARGET, 'TN_BATCH_SIZE': BATCH_SIZE})
  bench('baselines/parallel-policer/dpdk', 'pol', 'dpdk-parallel', {'RTE_SDK': RTE_SDK, 'RTE_TARGET': RTE_TARGET})
  bench('baselines/parallel-policer/dpdk', 'pol', 'dpdk-parallel', {'RTE_SDK': RTE_SDK, 'RTE_TARGET': RTE_TARGET, 'TN_BATCH_SIZE': BATCH_SIZE})

# Vigor NFs, as well as batched NAT for latency
if 0:
  for nf in ['nat', 'bridge', 'fw', 'pol', 'lb']:
    bench_vigor(nf, {})
  for nf in ['nat', 'bridge', 'fw', 'pol', 'lb']:
    bench_vigor(nf, {'RTE_SDK': RTE_SDK, 'RTE_TARGET': RTE_TARGET})
  bench_vigor('nat', {'RTE_SDK': RTE_SDK, 'RTE_TARGET': RTE_TARGET, 'TN_BATCH_SIZE': BATCH_SIZE})

# Click no-op with TinyNF vs DPDK vs DPDK batch
if 0:
  bench('baselines/click', 'nop', 'click', {})
  bench('baselines/click/with-dpdk', 'nop', 'click', {'RTE_SDK': RTE_SDK, 'RTE_TARGET': RTE_TARGET})
  bench('baselines/click/with-dpdk', 'nop', 'click', {'RTE_SDK': RTE_SDK, 'RTE_TARGET': RTE_TARGET, 'TN_BATCH_SIZE': BATCH_SIZE})

# DPDK l3fwd, which should reach 2x10 Gb/s line rate, as indicated in the DPDK perf reports
if 0:
  bench('baselines/dpdk/l3fwd', 'l3fwd', 'dpdk', {'RTE_SDK': RTE_SDK, 'RTE_TARGET': RTE_TARGET})
