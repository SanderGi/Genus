"""Replay and check all seven exceptional-prime certificates.

Reads exceptional_certificates.json by default, independently of the working
directory. The five compact records are used directly: no parameter or switch
search is performed. The final Q1/Q2 check uses the manuscript's equations,
not the constructor's face-verification routine.
"""
from __future__ import annotations

import argparse
import json
from math import isqrt
from pathlib import Path

import kneser_constructor as constructor

HERE = Path(__file__).resolve().parent
DEFAULT_CERTIFICATES = HERE / "exceptional_certificates.json"
EXCEPTIONAL_PRIMES = (11, 19, 43, 59, 67, 83, 107)


def verify_base_certificate(certificate: dict) -> dict:
    """Check the entire connection set, one cycle, and Q1/Q2 independently."""
    h, u = certificate["h"], certificate["u"]
    if (type(h) is not int or h < 11 or h % 8 != 3
            or any(h % p == 0 for p in range(2, isqrt(h) + 1))):
        raise ValueError("h must be a prime greater than 3, congruent to 3 modulo 8")
    q = (h - 1) // 2
    if type(u) is not int or not 1 < u < h:
        raise ValueError("Invalid square generator u")
    powers = [pow(u, k, h) for k in range(q)]
    if pow(u, q, h) != 1 or len(set(powers)) != q:
        raise ValueError("u must have order q modulo h")
    raw = certificate["cycle"]
    if (not isinstance(raw, (list, tuple))
            or any(not isinstance(s, (list, tuple)) or len(s) != 2
                   or any(type(x) is not int for x in s) for s in raw)):
        raise ValueError("cycle must contain integer pairs")
    cycle = [tuple(s) for s in raw]
    expected = {(c, k) for k, a in enumerate(powers) for c in range(h)
                if c not in {0, 1, -a % h, (1 - a) % h}}
    d = (h - 2) * (h - 3) // 2
    if len(cycle) != d or set(cycle) != expected:
        raise ValueError("The cycle must list each element of S exactly once")
    # The list defines one cyclic permutation, not a collection of cycles.
    rho = {s: cycle[(i + 1) % d] for i, s in enumerate(cycle)}
    predecessor = {t: s for s, t in rho.items()}

    def inverse(s):
        c, k = s
        return (-powers[-k % q] * c % h, -k % q)

    def multiply(s, t):
        c, k = s
        b, ell = t
        return ((c + powers[k] * b) % h, (k + ell) % q)

    for s0 in cycle:
        s1 = predecessor[inverse(s0)]
        s2 = rho[inverse(s1)]
        s3 = predecessor[inverse(s2)]
        if multiply(multiply(multiply(s0, s1), s2), s3) != (0, 0):
            raise ValueError(f"Q1 failed at {s0}")
        if rho[inverse(s3)] != s0:
            raise ValueError(f"Q2 failed at {s0}")
        if multiply(s0, s1) == (0, 0) or multiply(s1, s2) == (0, 0):
            raise ValueError("The quadrilateral repeats a vertex")
    vertices = h * (h - 1)
    edges = vertices * d // 2
    faces = edges // 2
    return {
        "h": h, "u": u, "base_cycle_length": d,
        "vertices": vertices, "edges": edges, "faces": faces,
        "genus": (2 - vertices + edges - faces) // 2,
        "single_cycle": True, "Q1_checked": d, "Q2_checked": d,
        "all_faces_length_four": True,
    }


def load_records(path: Path = DEFAULT_CERTIFICATES) -> dict:
    records = json.loads(Path(path).read_text(encoding="utf-8"))
    if not isinstance(records, dict):
        raise ValueError("Expected a JSON object keyed by prime")
    keys = {key for key in records if not key.startswith("_")}
    if keys != {str(h) for h in EXCEPTIONAL_PRIMES}:
        raise ValueError("Expected exactly the seven exceptional primes")
    for h in EXCEPTIONAL_PRIMES:
        record = records[str(h)]
        if not isinstance(record, dict) or type(record.get("h")) is not int or record["h"] != h:
            raise ValueError(f"Invalid record for h={h}")
        if ("base_cycle" in record) != (h in (11, 19)):
            raise ValueError("Use full cycles for 11 and 19, and compact records otherwise")
    return records


def verify_all_exceptional(path: Path = DEFAULT_CERTIFICATES,
                           write_cycles: Path | None = None) -> list[dict]:
    records = load_records(path)
    if write_cycles is not None:
        write_cycles.mkdir(parents=True, exist_ok=True)
    reports = []
    for h in EXCEPTIONAL_PRIMES:
        record = records[str(h)]
        certificate = constructor.construct_from_record(record)
        report = verify_base_certificate(certificate)
        if h > 19:
            z, switches = certificate["report"]["z"], certificate["report"]["small"]
            used = {"A": z["A"], "j": z["j"], "upsilon": z["ell"],
                    "outside_mask": switches["outside_mask"],
                    "interval_mask": switches["interval_mask"],
                    "forward_interval_maps": ["".join(map(str, p))
                                              for p in switches["transfer"]]}
            if any(used[key] != record[key] for key in used):
                raise ValueError(f"The construction did not use the stored record for {h}")
            report["compact_record_replayed"] = used
        if write_cycles is not None:
            output = {"h": h, "u": certificate["u"], "cycle": certificate["cycle"]}
            (write_cycles / f"h{h}_base_rotation.json").write_text(
                json.dumps(output, separators=(",", ":")) + "\n", encoding="utf-8")
        reports.append(report)
    return reports


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--certificates", type=Path, default=DEFAULT_CERTIFICATES)
    parser.add_argument("--output", type=Path, help="write the verification report")
    parser.add_argument("--write-cycles", type=Path, help="also write all seven full base cycles")
    args = parser.parse_args()
    try:
        result = {"exceptional_primes": verify_all_exceptional(
            args.certificates, args.write_cycles)}
        text = json.dumps(result, indent=2) + "\n"
        if args.output is not None:
            args.output.write_text(text, encoding="utf-8")
        print(text, end="")
    except (OSError, ValueError, KeyError, TypeError, AssertionError) as error:
        parser.exit(1, f"verification failed: {error}\n")


if __name__ == "__main__":
    main()
