#!/usr/bin/python3
# TODO: carefully review all drivers and come up with a clear classification methodology for exclusion

import common
import subprocess

# null: does nothing
# kni: indirection to DPDK's libkni, talks to kernel
# af_packet: indirection to BSD sockets
# af_xdp: another kind of af_ indirection
# pcap: indirection to libpcap
# vhost: indirection to DPDK's libvhost, which talks to virtio (but there is already a virtio driver)
# ring: in-memory loopback
# failsafe: adds hotplug support to drivers
# bonding: allows using multiple NICs as one
# vdev_netvsc: Hyper-V virtual NICs
# nfb: for a FPGA NIC, but uses an external library
def talks_to_hw(driver):
  return driver not in ['null', 'kni', 'af_packet', 'af_xdp', 'pcap', 'vhost', 'ring', 'failsafe', 'bonding', 'vdev_netvsc', 'nfb']

result = subprocess.check_output(['sh', '-c', "for d in $(ls -1 -d $RTE_SDK/drivers/net/*/); do echo $(cloc --quiet --exclude-lang=make $d | tail -n 2 | head -n 1 | awk '{print $5}') $(basename $d); done | sort -n"]).decode('utf-8').strip()

splits = [line.split(' ') for line in result.split('\n') if talks_to_hw(line.split(' ')[1])]
x = list(range(len(splits)))
y = [float(split[0]) / 1000.0 for split in splits]
labels = [split[1] for split in splits]

plt, ax, _ = common.get_pyplot_ax_fig(figsize=[6.6, 2.4])
ax.set_ylabel('Thousands of lines of code')
ax.bar(x, y)
ax.set_xticks(x)
ax.set_xticklabels(labels, rotation=60, ha='right')
ax.set_ylim(bottom=0)
ax.margins(x=0)

# ax tick for 1000LoC
#ax.axhline(1.0, color='xkcd:dark grey', linestyle='--')
ax.set_yticks([t for t in ax.get_yticks() if t != 0] + [1])

common.save_plot(plt, 'driver-loc')

print("Min LoC is", min(y))
print("Max LoC is", max(y))
