# SPDX-FileCopyrightText: 2026 Alexander Metzger
# SPDX-License-Identifier: GPL-2.0-only
"""Benchmark fresh (3,12)-cage exports, optionally timing PAGE separately."""

import argparse
import json
import platform
import statistics
import subprocess
import sys
import tempfile
import time
from pathlib import Path


def main():
    repo = Path(__file__).resolve().parents[1]
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--runs", type=int, default=3)
    parser.add_argument("--binary", type=Path, default=repo / "MultiGenus/planar_draw")
    parser.add_argument("--page", action="store_true", help="Find the rotation with PAGE first")
    args = parser.parse_args()
    if args.runs < 1:
        parser.error("--runs must be positive")
    if args.page:
        sys.path.insert(0, str(repo / "src"))
        import graph_genus
        graph = [list(map(int, row.split())) for row in
                 (repo / "PAGE/adjacency_lists/3-12-cage.txt").read_text().splitlines()[1:]]
        start = time.perf_counter()
        genus, rotation = graph_genus.embed(graph)
        print(f"PAGE: genus {genus}, {time.perf_counter() - start:.3f} s")
        if genus != 17:
            raise RuntimeError(f"Unexpected cage genus: {genus}")
    else:
        rotation = json.loads((repo / "tests/fixtures/3-12-cage-genus17.json").read_text())
    code = bytes([len(rotation)] + [value for row in rotation
                 for value in [*[v + 1 for v in row], 0]])
    timings = []
    with tempfile.TemporaryDirectory() as directory:
        prefix = Path(directory) / "cage"
        for _ in range(args.runs):
            start = time.perf_counter()
            result = subprocess.run([str(args.binary.resolve()), "f", "l", "o", str(prefix)],
                                    input=code, capture_output=True, timeout=60)
            timings.append(time.perf_counter() - start)
            if result.returncode:
                raise RuntimeError(result.stderr.decode())
            obj = prefix.with_suffix(".obj").read_text()
            if sum(line.startswith("l ") for line in obj.splitlines()) != 189:
                raise RuntimeError("Incomplete cage export")
        print(f"Fresh layout + OBJ export ({platform.machine()}): "
              + ", ".join(f"{t:.3f} s" for t in timings))
        print(f"Median: {statistics.median(timings):.3f} s; OBJ: {len(obj.encode()) / 1e6:.2f} MB")


if __name__ == "__main__":
    main()
