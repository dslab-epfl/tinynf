#!/usr/bin/python3

from common import *
import subprocess

# null: does nothing
# kni: indirection to DPDK's libkni, talks to kernel
# af_packet: indirection to BSD sockets
# pcap: indirection to libpcap
# vhost: indirection to DPDK's libvhost, which talks to virtio (but there is already a virtio driver)
# ring: in-memory loopback
# failsafe: adds hotplug support to drivers
# bonding: allows using multiple NICs as one
def talks_to_hw(driver):
  return driver != 'null' and driver != 'kni' and driver != 'af_packet' and driver != 'pcap' and driver != 'vhost' and driver != 'ring' and driver != 'failsafe' and driver != 'bonding'

result = subprocess.check_output(['sh', '-c', "for d in $(ls -1 -d $RTE_SDK/drivers/net/*/); do echo $(cloc --quiet --exclude-lang=make $d | tail -n 2 | head -n 1 | awk '{print $5}') $(basename $d); done | sort -n"]).decode('utf-8').strip()

splits = [line.split(' ') for line in result.split('\n') if talks_to_hw(line.split(' ')[1])]
x = list(range(len(splits)))
y = [int(split[0]) for split in splits]
labels = [split[1] for split in splits]

plt, ax = get_pyplot_ax('', figsize=[6.6, 2.4])
ax.set_ylabel('Lines of code')
ax.bar(x, y)
ax.set_xticks(x)
ax.set_xticklabels(labels, rotation=60, ha='right')
ax.set_ylim(bottom=0)
ax.margins(x=0)

# line for 1000LoC
ax.axhline(1000, color='xkcd:dark grey', linestyle='--')
ax.set_yticks([t for t in ax.get_yticks() if t != 0] + [1000])

plt.savefig('driver-loc.svg', bbox_inches='tight', pad_inches=0)
