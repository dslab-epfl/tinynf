#!/usr/bin/python3

import math
import os

THIS_DIR = os.path.dirname(os.path.realpath(__file__))

def percentile(list, n):
  size = len(list)
  return sorted(list)[int(math.ceil((size * n) / 100)) - 1]

def get_pyplot_ax(title, figsize=None):
  import matplotlib as mpl
  mpl.use('Agg') # avoid the need for an X server

  import matplotlib.pyplot as plt
  # avoid unnecessary margins
  plt.rcParams['axes.ymargin'] = 0
  plt.rcParams['axes.xmargin'] = 0

  fig = plt.figure(figsize=figsize)
  # put the title inside the plot to save space
  fig.suptitle(title, y=0.85)

  ax = fig.add_subplot(1, 1, 1)
  # Remove top and right spines
  ax.spines['top'].set_visible(False)
  ax.spines['right'].set_visible(False)

  return (plt, ax)

def get_color_label_marker(nf):
  # same colors as the figures
  if 'ixy' in nf:
    if 'batched' in nf:
      return ('#203864', 'Ixy, batched', 'X')
    return ('#4472C4', 'Ixy', 'x')
  if 'dpdk' in nf:
    if 'batched' in nf:
      return ('#843C0C', 'DPDK, batched', '^')
    return ('#ED7D31', 'DPDK', 'v')
  return ('#70AD47', 'TinyNF', 'P') # P == filled plus

def save_plot(plt, name):
  plot_dir = THIS_DIR + '/plots/'
  os.makedirs(plot_dir, exist_ok=True)
  plt.savefig(plot_dir + name + '.svg', bbox_inches='tight', pad_inches=0.01)
