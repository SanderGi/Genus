#!/usr/bin/env python3
# SPDX-FileCopyrightText: 2026 Alexander Metzger
# SPDX-License-Identifier: GPL-2.0-only
"""Run the benchmarks and tests from docs/practical_performance.md."""

import re, subprocess, time
from pathlib import Path

TIMEOUT = 90

# Identify the graphs that finish in finite time in the docs
rows = []
for line in Path("../docs/practical_performance.md").read_text().splitlines():
    m = re.search(r"\((\.\./PAGE/adjacency_lists/[^)]+)\)", line)
    if not m:
        continue
    cells = [c.strip() for c in line.split("|")]
    if len(cells) >= 10:
        genus, page_time = cells[-4], cells[-3]
    elif len(cells) >= 6:
        genus, page_time = cells[-3], cells[-2]
    else:
        continue
    if not re.fullmatch(r"\d+", genus):
        continue
    if not re.fullmatch(r"\d+(?:\.\d+)?", page_time):
        continue
    path = m.group(1).replace("../PAGE/", "")
    rows.append((path, int(genus)))

# Run the graphs
fail = []
start_time = time.perf_counter()
for idx, (path, expected) in enumerate(rows, 1):
    path = (
        "../MultiGenus/"
        + path.removesuffix(".txt").replace("adjacency_lists", "graphs")
        + ".mc"
    )
    with open(path, "rb") as f:
        multicode = f.read()

    t = time.perf_counter()
    cmd = ["./genus", "--multicode"]
    try:
        cp = subprocess.run(cmd, input=multicode, capture_output=True, timeout=TIMEOUT)
    except subprocess.TimeoutExpired:
        dt = time.perf_counter() - t
        print(
            f"{idx:02d}/{len(rows)} TIMEOUT {path} expected={expected} after {dt:.1f}s",
            flush=True,
        )
        fail.append((path, "timeout", expected, None))
        continue
    got = int(cp.stdout.decode())
    status = "OK" if cp.returncode == 0 and got == expected else "FAIL"
    print(
        f"{idx:02d}/{len(rows)} {status} {path} expected={expected} got={got} time={time.perf_counter()-t:.3f}s",
        flush=True,
    )
    if status != "OK":
        fail.append((path, cp.returncode, expected, got))

print("TOTAL", time.perf_counter() - start_time, "failures", len(fail))
for f in fail:
    print("FAILDETAIL", f)
