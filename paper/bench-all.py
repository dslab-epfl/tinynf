#!/usr/bin/python3
from distutils.dir_util import copy_tree
import os
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

def has_dpdk(env):
  return 'RTE_SDK' in env

# --- per-NF parameters ---

def get_key(nf, kind, env):
  suffix = ''
  if has_dpdk(env):
    if env['RTE_TARGET'] == '.':
      suffix += '-shimmed'
    else:
      suffix += '-dpdk'
  if env.get('TN_BATCH_SIZE', '1') != '1':
    suffix += '-batched'
  return kind + '-' + nf + suffix

def get_env(nf, kind, env):
  result = {}
  result['TN_DEBUG'] = '0'
  if kind == 'vigor':
    result['TN_NF'] = nf
    # Expiration time default is 10us which is nothing
    result['EXPIRATION_TIME'] = '4000000'
    # Bridge needs flows in both directions
    if nf == 'bridge':
      result['CAPACITY'] = '131072'
    # Policer needs large maximums so as to not really police, since we measure throughput
    if nf == 'pol':
      result['POLICER_BURST'] = '10000000000'
      result['POLICER_RATE'] = '10000000000'
    if nf == 'lb':
      # Device from which the load balancer will receive packets (and not heartbeats)
      result['WAN_DEVICE'] = '0'
  if kind == 'click':
    result['TN_NF'] = nf
  return result

def get_benchflags(nf, kind, env):
  if nf == 'lb':
    # LB needs reverse heatup to work
    return ['-r']
  return []

def get_cflags(nf, kind, env):
  result = []
  if not has_dpdk(env) or env['RTE_TARGET'] == '.':
    result.append('-flto')
    if kind == 'vigor' and nf == 'bridge':
      result.append('-DIXGBE_AGENT_OUTPUTS_MAX=2')
    else:
      result.append('-DIXGBE_AGENT_OUTPUTS_MAX=1')
      result.append('-DASSUME_ONE_WAY')
  return result

def get_layer(nf, kind, env):
  if nf == 'nat' or nf == 'lb' or nf == 'fw':
    return 4
  if nf == 'pol':
    return 3
  return 2


# --- benchmarking ---

def bench_core(nf, kind, nf_dir, benchflags, additional_env):
  # Just in case...
  subprocess.call(['sh', '-c', 'sudo rm -rf /dev/hugepages/*'])

  env = dict(os.environ)
  env.update(get_env(nf, kind, env))
  env.update(additional_env)
  env['TN_CFLAGS'] = " ".join(get_cflags(nf, kind, env))
  env['TN_LDFLAGS'] = env['TN_CFLAGS'] # TODO this should not be needed, fix makefiles

  benchflags = get_benchflags(nf, 'vigor', env) + benchflags + [str(get_layer(nf, kind, env))]

  while True: # bench.sh can fail for spurious reasons, e.g. random DNS failures during SSH login
    result = subprocess.run(['sh', 'bench.sh', nf_dir] + benchflags, cwd=BENCH_PATH, env=env).returncode
    if result == 0:
      break
    else:
      time.sleep(60)

def bench_vigor(nf, env):
  print('[ !!! ] Benchmarking', nf, 'in the Vigor way')
  bench_core(nf, 'vigor', THIS_DIR + '/../baselines/vigor', ['--latencyload=1000', 'standard-single'], env)
  add_suffix(BENCH_RESULT_TPUT_PATH, '-single')
  add_suffix(BENCH_RESULT_LATS_PATH, '-single')
  move_into(BENCH_RESULTS_PATH, 'results/' + get_key(nf, 'vigor', env))

def bench(path, nf, kind, env):
  print('[ !!! ] Benchmarking', kind, nf, 'in', path)
  out_folder = 'results/' + get_key(nf, kind, env)
  bench_core(nf, kind, THIS_DIR + '/../' + path, ['standard'], env)
  move_into(BENCH_RESULTS_PATH, out_folder)
  bench_core(nf, kind, THIS_DIR + '/../' + path, ['--acceptableloss=0', '--latencyload=-1', 'standard'], env)
  add_suffix(BENCH_RESULT_TPUT_PATH, '-zeroloss')
  move_into(BENCH_RESULT_TPUT_PATH + '-zeroloss', out_folder)


# First comparison: DPDK's testpmd no-op, batched or not, vs TinyNF no-op vs Ixy no-op (throughput, zero-loss throughput, detailed latency)
bench('code', 'nop', 'tinynf', {})
bench('baselines/dpdk', 'nop', 'testpmd', {'RTE_SDK': RTE_SDK, 'RTE_TARGET': RTE_TARGET})
bench('baselines/dpdk', 'nop', 'testpmd', {'RTE_SDK': RTE_SDK, 'RTE_TARGET': RTE_TARGET, 'TN_BATCH_SIZE': BATCH_SIZE})
bench('baselines/ixy', 'nop', 'ixyfwd', {})
bench('baselines/ixy', 'nop', 'ixyfwd', {'TN_BATCH_SIZE': BATCH_SIZE})

# Second comparison: VigNAT with TinyNF vs TinyNF-DPDK-shim vs DPDK vs DPDK batched
bench('baselines/vigor', 'nat', 'vigor', {})
bench('baselines/vigor/with-dpdk', 'nat', 'vigor', {'RTE_SDK': RTE_FAKE_SDK, 'RTE_TARGET': RTE_FAKE_TARGET})
bench('baselines/vigor/with-dpdk', 'nat', 'vigor', {'RTE_SDK': RTE_SDK, 'RTE_TARGET': RTE_TARGET})
bench('baselines/vigor/with-dpdk', 'nat', 'vigor', {'RTE_SDK': RTE_SDK, 'RTE_TARGET': RTE_TARGET, 'TN_BATCH_SIZE': BATCH_SIZE})

# Third comparison: Vigor NFs
for nf in ['nat', 'bridge', 'fw', 'pol', 'lb']:
  bench_vigor(nf, {})
  bench_vigor(nf, {'RTE_SDK': RTE_SDK, 'RTE_TARGET': RTE_TARGET})

# Fourth comparison: Click no-op with TinyNF vs DPDK vs DPDK batch
#bench('baselines/click', 'nop', 'click', {})
#bench('baselines/click/with-dpdk', 'nop', 'click', {'RTE_SDK': RTE_SDK, 'RTE_TARGET': RTE_TARGET})
#bench('baselines/click/with-dpdk', 'nop', 'click', {'RTE_SDK': RTE_SDK, 'RTE_TARGET': RTE_TARGET, 'TN_BATCH_SIZE': BATCH_SIZE})
