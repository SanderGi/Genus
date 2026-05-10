#!/usr/bin/env python3
"""Run CalcGenus against the GitHub issue regression fixtures."""

from __future__ import annotations

import os
import re
import subprocess
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent
ADJ_DIR = ROOT / "adjacency_lists"

CASES = [
    ("issue2_quartic_counterexample.txt", 2, 2, "issue #2 quartic counterexample"),
    ("issue3_01886.txt", 1, "issue #3 graph6 1886:H??FFz{"),
    ("issue3_01995.txt", 1, "issue #3 graph6 1995:H??FfZ{"),
    ("issue3_02060.txt", 1, "issue #3 graph6 2060:H??Fvjk"),
    ("issue3_06412.txt", 1, "issue #3 graph6 6412:H?ABfp{"),
    ("issue3_06549.txt", 1, "issue #3 graph6 6549:H?ABv`{"),
    ("issue3_06632.txt", 1, "issue #3 graph6 6632:H?ABvp{"),
    ("issue3_09528.txt", 1, "issue #3 graph6 9528:H?AFBx{"),
    ("issue3_10533.txt", 1, "issue #3 graph6 10533:H?AFFp{"),
    ("issue3_10820.txt", 1, "issue #3 graph6 10820:H?AFbZw"),
    ("issue3_10877.txt", 1, "issue #3 graph6 10877:H?AFbx{"),
    ("issue3_11085.txt", 1, "issue #3 graph6 11085:H?AFfP{"),
    ("issue3_11263.txt", 1, "issue #3 graph6 11263:H?AFfp{"),
    ("issue3_11388.txt", 1, "issue #3 graph6 11388:H?AFvp{"),
    ("issue3_13015.txt", 1, "issue #3 graph6 13015:H?B@hzw"),
    ("issue3_13685.txt", 1, "issue #3 graph6 13685:H?B@nRw"),
    ("issue3_13793.txt", 1, "issue #3 graph6 13793:H?B@nrw"),
    ("issue3_13905.txt", 1, "issue #3 graph6 13905:H?B@pzw"),
    ("issue3_14290.txt", 1, "issue #3 graph6 14290:H?B@trw"),
    ("issue3_14712.txt", 1, "issue #3 graph6 14712:H?B@vrw"),
    ("issue3_14752.txt", 1, "issue #3 graph6 14752:H?B@xzw"),
    ("issue3_14805.txt", 1, "issue #3 graph6 14805:H?B@|pw"),
    ("issue3_14827.txt", 1, "issue #3 graph6 14827:H?B@|ro"),
    ("issue3_14833.txt", 1, "issue #3 graph6 14833:H?B@|rw"),
    ("issue3_14929.txt", 1, "issue #3 graph6 14929:H?B@~bg"),
    ("issue3_18479.txt", 1, "issue #3 graph6 18479:H?BD`zw"),
    ("issue3_18944.txt", 1, "issue #3 graph6 18944:H?BDbrw"),
    ("issue3_19534.txt", 1, "issue #3 graph6 19534:H?BDdrw"),
    ("issue3_20568.txt", 1, "issue #3 graph6 20568:H?BDfrw"),
    ("issue3_21492.txt", 1, "issue #3 graph6 21492:H?BDrro"),
    ("issue3_21498.txt", 1, "issue #3 graph6 21498:H?BDrrw"),
    ("issue3_21556.txt", 1, "issue #3 graph6 21556:H?BDtpw"),
    ("issue3_21578.txt", 1, "issue #3 graph6 21578:H?BDtrw"),
    ("issue3_21753.txt", 1, "issue #3 graph6 21753:H?BDvbw"),
    ("issue3_21837.txt", 1, "issue #3 graph6 21837:H?BDvrw"),
    ("issue3_22317.txt", 1, "issue #3 graph6 22317:H?BEFo}"),
    ("issue3_22865.txt", 1, "issue #3 graph6 22865:H?BF@zw"),
    ("issue3_23776.txt", 1, "issue #3 graph6 23776:H?BFFrw"),
    ("issue3_24423.txt", 1, "issue #3 graph6 24423:H?BFfRw"),
    ("issue3_24557.txt", 1, "issue #3 graph6 24557:H?BFfrw"),
    ("issue3_24665.txt", 1, "issue #3 graph6 24665:H?BFvrw"),
    ("issue3_24799.txt", 1, "issue #3 graph6 24799:H?Bcrbw"),
    ("issue3_25219.txt", 1, "issue #3 graph6 25219:H?BcvBw"),
    ("issue3_25304.txt", 1, "issue #3 graph6 25304:H?Bcv`w"),
    ("issue3_26006.txt", 1, "issue #3 graph6 26006:H?BeeRw"),
    ("issue3_26357.txt", 1, "issue #3 graph6 26357:H?BefRw"),
    ("issue3_26473.txt", 1, "issue #3 graph6 26473:H?Befrw"),
    ("issue3_26944.txt", 1, "issue #3 graph6 26944:H?Beurw"),
    ("issue3_27060.txt", 1, "issue #3 graph6 27060:H?Bevbw"),
    ("issue3_27280.txt", 1, "issue #3 graph6 27280:H?BfEo]"),
    ("issue3_27314.txt", 1, "issue #3 graph6 27314:H?BfErw"),
    ("issue3_27470.txt", 1, "issue #3 graph6 27470:H?BfFrw"),
    ("issue3_27669.txt", 1, "issue #3 graph6 27669:H?BffRw"),
    ("issue3_27791.txt", 1, "issue #3 graph6 27791:H?Bffrw"),
    ("issue3_28094.txt", 1, "issue #3 graph6 28094:H?BvfRw"),
    ("issue3_28146.txt", 1, "issue #3 graph6 28146:H?Bvfrw"),
    ("issue3_41966.txt", 1, "issue #3 graph6 41966:H?`F`zo"),
    ("issue3_09528.txt", 1, "issue #4 graph6 H?AFBx{"),
    ("issue3_18479.txt", 1, "issue #4 graph6 H?BD`zw"),
    ("issue3_18944.txt", 1, "issue #4 graph6 H?BDbrw"),
]

GENUS_PATTERNS = [
    re.compile(r"Solution with \d+ cycles \(genus (\d+)\)"),
    re.compile(r"Found a solution! The genus is (\d+)"),
    re.compile(r"Genus found: (\d+)"),
    re.compile(r"Found the genus! It is (\d+)"),
]


def read_degree(path: Path) -> int:
    lines = [line.strip() for line in path.read_text().splitlines() if line.strip()]
    if len(lines) < 2:
        raise ValueError(f"{path} does not contain adjacency rows")
    return len(lines[1].split())


def extract_genus(output: str) -> int | None:
    for pattern in GENUS_PATTERNS:
        match = pattern.search(output)
        if match:
            return int(match.group(1))
    return None


def run_case(case: tuple) -> tuple[bool, str]:
    if len(case) == 3:
        filename, expected, label = case
        glb = None
    else:
        filename, expected, glb, label = case
    path = ADJ_DIR / filename
    env = os.environ.copy()
    env.update({"S": "0", "DEG": str(read_degree(path)), "ADJ": str(path), "STDOUT": "1", "PBN": "1"})
    if glb is not None:
        env["GLB"] = str(glb)
    result = subprocess.run(
        [str(ROOT / "CalcGenus")],
        cwd=ROOT,
        env=env,
        text=True,
        capture_output=True,
        timeout=30,
    )
    output = result.stdout + result.stderr
    actual = extract_genus(output)
    if result.returncode != 0:
        return False, f"{label}: CalcGenus exited {result.returncode}\n{output[-1200:]}"
    if actual != expected:
        return False, f"{label}: expected genus {expected}, got {actual}\n{output[-1200:]}"
    return True, f"{label}: genus {actual}"


def main() -> int:
    subprocess.run(["make"], cwd=ROOT, check=True)
    failures = []
    for case in CASES:
        ok, message = run_case(case)
        print(("PASS" if ok else "FAIL"), message)
        if not ok:
            failures.append(message)
    if failures:
        print(f"\n{len(failures)} issue regression(s) failed", file=sys.stderr)
        return 1
    print(f"\n{len(CASES)} issue regression(s) passed")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
