"""Emit only the numeric witnesses for the Lean proofs in Exceptional.lean."""

from pathlib import Path
import sys

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE.parent))
from verify_exceptional import EXCEPTIONAL_PRIMES, constructor, load_records


def packed(values, bits):
    """Encode bounded natural numbers as little-endian bit fields."""
    if any(not 0 <= x < 1 << bits for x in values):
        raise ValueError("Entry does not fit in the field width")
    return hex(sum(x << (bits * i) for i, x in enumerate(values)))


def tables(record):
    certificate = constructor.construct_from_record(record)
    h, u = certificate["h"], certificate["u"]
    q = (h - 1) // 2
    d = (h - 2) * (h - 3) // 2
    bits = (h * q).bit_length()
    powers = [pow(u, k, h) for k in range(q)]
    labels = [c * q + k for c, k in certificate["cycle"]]
    indices = [0] * (h * q)
    for i, label in enumerate(labels):
        indices[label] = i
    logs = [0] * h
    for k, a in enumerate(powers):
        logs[a], logs[h - a] = k, q + k
    return f"""
/-- Proposed base cycle for h = {h}. -/
def cycle{h} : BaseCycle {h} {q} {d} :=
  unpack {bits} {packed(powers, bits)} {packed(labels, bits)} {packed(indices, bits)}

/-- Proposed inverse vertex chart for h = {h}. -/
def decode{h} : Fin {h} → Fin {h} → Frame {h} {q} :=
  decodePair {bits} {packed(logs, bits)}
"""


def main():
    records = load_records()
    print("import BipartiteKneser.Certificates")
    print("namespace BipartiteKneser.Exceptional")
    for h in EXCEPTIONAL_PRIMES:
        print(tables(records[str(h)]))
    print("end BipartiteKneser.Exceptional")


if __name__ == "__main__":
    main()
