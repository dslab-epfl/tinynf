#!/usr/bin/python3

import subprocess
import sys

sys.path.append("..")
import common

subprocess.check_output(["sh", "-c", "git submodule update --init --recursive"])

print("Counting and graphing lines of code, this will take less than a minute...")

result = subprocess.check_output(["sh", "-c", "sed -e '0,/| Name/d' dpdk-drivers.md | tail -n+2 | grep '|\s*yes\s*|' | cut -d '|' -f 2"]).decode('utf-8').strip()
drivers = [line.strip() for line in result.split('\n')]
locs = [(d, float(subprocess.check_output(["sh", "-c", "cloc --quiet --exclude-lang=make,build ../../baselines/dpdk/dpdk/drivers/net/" + d + " | grep '^SUM:' | awk '{print $5}'"]).decode('utf-8').strip()) / 1000.0) for d in drivers]
locs.sort(key=lambda t: t[1])
x = list(range(len(locs)))
y = [t[1] for t in locs]
labels = [t[0] for t in locs]

print("Smallest driver is", locs[0][0], "with", int(locs[0][1] * 1000), "LoC")
print("Biggest driver is", locs[-1][0], "with", int(locs[-1][1] * 1000), "LoC")
print("(these stats exclude drivers not for NIC dataplane hardware)")
print()

plt, ax, _ = common.get_pyplot_ax_fig(figsize=[6.6, 2.4])
ax.set_ylabel('Thousands of lines of code')
ax.bar(x, y)
ax.set_xticks(x)
ax.set_xticklabels(labels, rotation=60, ha='right')
ax.set_ylim(bottom=0)
ax.set_yticks([t for t in ax.get_yticks() if t != 0] + [1])
ax.margins(x=0)

common.save_plot(plt, 'dpdk-drivers-loc')
print("Done! Saved to ../plots/dpdk-drivers-loc.svg")
