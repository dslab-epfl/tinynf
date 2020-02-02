#!/usr/bin/python3

import math
import os

this_dir = os.path.dirname(os.path.realpath(__file__))

def percentile(list, n):
  size = len(list)
  return sorted(list)[int(math.ceil((size * n) / 100)) - 1]

def get_pyplot_ax(title, figsize=None):
  import matplotlib as mpl
  mpl.use('Agg') # avoid the need for an X server
  import matplotlib.pyplot as plt
  fig = plt.figure(figsize=figsize)
  fig.suptitle(title, y=0.85) # put the title inside the plot to save space
  ax = fig.add_subplot(1, 1, 1)
  # Remove top and right spines
  ax.spines['top'].set_visible(False)
  ax.spines['right'].set_visible(False)
  return (plt, ax)

def get_output_folder(kind, nf):
  return this_dir + '/results/' + kind + '/' + nf

def get_color(key):
  color = ''
  if key == 'original, batching':
    color = 'goldenrod'
  elif key == 'original':
    color = 'gold'
  elif 'shim' in key:
    color = 'blue'
    if 'simple' in key:
      color = 'indigo'
  elif 'custom' in key:
    color = 'red'
    if 'simple' in key:
      color = 'brick red'

  return 'xkcd:' + color

def get_title(kind, nf):
  title = kind.title() + ' '
  if nf == 'nop':
    title += 'No-op'
  elif nf == 'nat':
    title += 'NAT'
  elif nf == 'bridge':
    title += 'Bridge'
  elif nf == 'pol':
    title += 'Policer'
  elif nf == 'fw':
    title += 'Firewall'
  else:
    title += ' ' + nf

  return title
