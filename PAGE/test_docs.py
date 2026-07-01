import os, re, subprocess, sys, time
from pathlib import Path

TIMEOUT = 90
# IMPLEMENTATION = "python"
# IMPLEMENTATION = "c"
IMPLEMENTATION = os.environ.get("IMPLEMENTATION", "c")

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
    vals = list(map(int, Path(path).read_text().split()))
    n = vals[0]
    degree = (len(vals) - 2) // n
    rows.append((path, degree, int(genus)))

# Run the graphs
fail = []
start_time = time.perf_counter()
for idx, (path, degree, expected) in enumerate(rows, 1):
    start = float("Inf")
    with open(path, "r") as f:
        lines = f.readlines()[1:]
        for line in lines:
            start = min(start, min(map(int, line.split())))

    t = time.perf_counter()
    env = os.environ.copy()
    if IMPLEMENTATION == "python":
        cmd = [
            sys.executable,
            "page.py",
            "--quiet",
            "--adj",
            path,
            "--degree",
            str(degree),
            "--start",
            str(start),
            "--out",
            "/tmp/page_test_docs.out",
        ]
    elif IMPLEMENTATION == "c":
        cmd = ["make", "run"]
        env["S"] = str(start)
        env["DEG"] = str(degree)
        env["ADJ"] = path
        env["STDOUT"] = "1"
    else:
        raise ValueError("Invalid implementation: must be 'python' or 'c'")
    try:
        cp = subprocess.run(
            cmd, text=True, capture_output=True, timeout=TIMEOUT, env=env
        )
    except subprocess.TimeoutExpired:
        dt = time.perf_counter() - t
        print(
            f"{idx:02d}/{len(rows)} TIMEOUT {path} expected={expected} after {dt:.1f}s",
            flush=True,
        )
        fail.append((path, "timeout", expected, None))
        continue
    out = cp.stdout + cp.stderr
    m = re.search(r"genus is (\d+)", out)
    got = int(m.group(1)) if m else None
    if got is None:
        m = re.search(r"It is (\d+)", out)
        got = int(m.group(1)) if m else None
    status = "OK" if cp.returncode == 0 and got == expected else "FAIL"
    print(
        f"{idx:02d}/{len(rows)} {status} {path} expected={expected} got={got} time={time.perf_counter()-t:.3f}s",
        flush=True,
    )
    if status != "OK":
        fail.append((path, cp.returncode, expected, got, out[-500:]))

print("TOTAL", time.perf_counter() - start_time, "failures", len(fail))
for f in fail:
    print("FAILDETAIL", f)
