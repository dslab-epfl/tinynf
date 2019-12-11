#!/usr/bin/python3

import os

this_dir = os.path.dirname(os.path.realpath(__file__))

def get_pyplot_ax(title):
  import matplotlib as mpl
  mpl.use('Agg') # avoid the need for an X server
  import matplotlib.pyplot as plt
  fig = plt.figure()
  fig.suptitle(title, y=0.85) # put the title inside the plot to save space
  ax = fig.add_subplot(1, 1, 1)
  # Remove top and right spines
  ax.spines['top'].set_visible(False)
  ax.spines['right'].set_visible(False)
  return (plt, ax)

def get_output_filename(kind, nf, name):
  return this_dir + '/results/' + kind + '/' + nf + '/' + name

def get_lat_dir(kind, nf, key, period):
  return this_dir + '/results/' + kind + '/' + nf + '/latencies/' + key + '/' + period

def get_color(key):
  color = ''
  if key == 'original, batching':
    color = 'goldenrod'
  elif key == 'original':
    color = 'gold'
  elif 'shim' in key:
    color = 'blue'
    if 'simple' in key:
      color = 'turquoise'
  elif 'custom' in key:
    color = 'red'
    if 'simple' in key:
      color = 'magenta'

  if 'LTO' not in key:
    color = 'light ' + color

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
