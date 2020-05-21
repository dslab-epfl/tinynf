#!/usr/bin/python3
from distutils.dir_util import copy_tree
import os
import subprocess
import time

RTE_SDK = '/home/solal/dpdk' # TODO FIXME
RTE_TARGET = 'x86_64-native-linuxapp-gcc'

THIS_DIR = os.path.dirname(os.path.realpath(__file__))
BENCH_DIR = THIS_DIR + '/../benchmarking/'
BENCH_RESULTS_PATH = BENCH_DIR + '/results'
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
      if 'TN_BATCH_SIZE' in env:
        suffix += '-batched'
  return kind + '-' + nf + suffix

def get_env(nf, kind='', with_dpdk=False):
  result = {}
  if kind == 'vigor':
    result['TN_NF'] = nf
    # Expiration time default is 10us which is nothing
    result['EXPIRATION_TIME'] = '4000000'
    # Bridge needs flows in both directions
    if nf == 'bridge':
      result['CAPACITY'] = '131072'
    # Policer needs large maximums so as to not really police, since we measure throughput
    if NF == 'pol':
      result['POLICER_BURST'] = '10000000000'
      result['POLICER_RATE'] = '10000000000'
    if NF == 'lb':
      # Device from which the load balancer will receive packets (and not heartbeats)
      result['WAN_DEVICE'] = '0'
  if kind == 'click':
    result['TN_NF'] = nf
  return result

def get_benchflags(nf, kind='', with_dpdk=False):
  if nf == 'lb':
    # LB needs reverse heatup to work
    return ['-r']
  return []

def get_cflags(nf, kind='', with_dpdk=False):
  result = []
  if not with_dpdk:
    result.append('-flto')
    if kind == 'vigor' and nf == 'bridge':
      result.append('-DIXGBE_AGENT_OUTPUTS_MAX=2')
    else:
      result.append('-DIXGBE_AGENT_OUTPUTS_MAX=1')
      result.append('-DASSUME_ONE_WAY')
  return result

def get_layer(nf, kind='', with_dpdk=False):
  if nf == 'nat' or nf == 'lb' or nf == 'fw':
    return 4
  if nf == 'pol':
    return 3
  return 2


# --- benchmarking ---

def bench_core(nf, kind, with_dpdk, nf_dir, benchflags, additional_env)
  with_dpdk = has_dpdk(additional_env)

  env = dict(os_environ)
  env.update(get_env(nf, kind, with_dpdk))
  env.update(additional_env)
  env['TN_CFLAGS'] = get_cflags(nf, kind, with_dpdk)
  env['TN_LDFLAGS'] = env['TN_CFLAGS'] # TODO this should not be needed, fix makefiles

  benchflags = get_benchflags(nf, 'vigor', with_dpdk) + benchflags + [get_layer(nf, kind, with_dpdk)]

  while True: # bench.sh can fail for spurious reasons, e.g. random DNS failures during SSH login
    print('[ !!! ] Benchmarking', nf, kind, 'dpdk:', with_dpdk, 'path:', nf_dir)
    result = subprocess.run(['sh', 'bench.sh', nf_dir] + benchflags cwd=BENCH_DIR, env=env).returncode
    if result == 0:
      break
    else:
      time.sleep(60)

def bench_vigor(nf, env):
  path_suffix = '/with-dpdk' if has_dpdk(env) else ''
  bench_core(nf, 'vigor', THIS_DIR + '/../baselines/vigor' + path_suffix, ['--latencyload=1000', 'standard-single'], env)
  add_suffix(BENCH_RESULT_TPUT_PATH, '-single')
  add_suffix(BENCH_RESULT_LATS_PATH, '-single')
  move_into(BENCH_RESULTS_PATH, 'results/' + get_key(nf, 'vigor', env))

def bench(path, nf, kind, env)
  path_suffix = '/with-dpdk' if has_dpdk(env) else ''
  out_folder = 'results/' + get_key(nf, kind, env)

  bench_core(nf, kind, THIS_DIR + '/../' + path + path_suffix, ['standard'], env)
  move_into(BENCH_RESULTS_PATH, out_folder)

  bench_core(nf, kind, THIS_DIR + '/../' + path + path_suffix, ['--acceptableloss=0', '--latencyload=-1', 'standard'], env)
  add_suffix(BENCH_RESULT_TPUT_PATH, '-zeroloss')
  move_into(BENCH_RESULT_TPUT_PATH, out_folder)


bench('code', 'nop', 'tinynf', {})
bench('baselines/dpdk', 'nop', 'dpdk', {'RTE_SDK': RTE_SDK, 'RTE_TARGET': RTE_TARGET})
bench('baselines/dpdk', 'nop', 'dpdk', {'RTE_SDK': RTE_SDK, 'RTE_TARGET': RTE_TARGET, 'TN_BATCH_SIZE': 32})

"""
# First comparison: DPDK's testpmd no-op, batched or not, vs TinyNF no-op (throughput, zero-loss throughput, detailed latency)
LTO, ONEWAY, bench TinyNF standard 2 -> move results
LTO, ONEWAY, bench TinyNF zero-accepted-loss no-latency standard 2 -> move throughput to special file
bench TestPMD standard 2
bench TestPMD zero-accepted-loss no-latency standard 2 -> move throughput to special file
BATCH bench TestPMD standard 2
BATCH bench TestPMD zero-accepted-loss no-latency standard 2 -> move throughput to special file

# Second comparison: VigNAT with TinyNF vs TinyNF-DPDK-shim vs DPDK vs DPDK batched
EXP_TIME FLOW_CAP LTO ONEWAY bench VigNAT standard 4 -> move results
EXP_TIME FLOW_CAP LTO ONEWAY bench VigNAT zero-accepted-loss no-latency standard 4 -> move throughput to special file
SHIM EXP_TIME FLOW_CAP LTO ONEWAY bench VigNAT standard 4 -> move results
SHIM EXP_TIME FLOW_CAP LTO ONEWAY bench VigNAT zero-accepted-loss no-latency standard 4 -> move throughput to special file
DPDK EXP_TIME FLOW_CAP LTO ONEWAY bench VigNAT standard 4 -> move results
DPDK EXP_TIME FLOW_CAP LTO ONEWAY bench VigNAT zero-accepted-loss no-latency standard 4 -> move throughput to special file
DPDK BATCH EXP_TIME FLOW_CAP LTO ONEWAY bench VigNAT standard 4 -> move results
DPDK BATCH EXP_TIME FLOW_CAP LTO ONEWAY bench VigNAT zero-accepted-loss no-latency standard 4 -> move throughput to special file

# Third comparison: Vigor NFs
for each vignf:
  PARAMS_OF(vignf) LTO ONEWAY_OF(vignf) bench vignf standard-single latency-1000 LAYER_OF(vignf) -> move results

# Fourth comparison: Click no-op with TinyNF vs DPDK vs DPDK batch
LTO, ONEWAY, bench Click standard 2 -> move results
LTO, ONEWAY, bench Click zero-accepted-loss no-latency standard 2 -> move throughput to special file
DPDK bench Click standard 2
DPDK bench Click zero-accepted-loss no-latency standard 2 -> move throughput to special file
DPDK BATCH bench TestPMD standard 2
DPDK BATCH bench TestPMD zero-accepted-loss no-latency standard 2 -> move throughput to special file
"""
