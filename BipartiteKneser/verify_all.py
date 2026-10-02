"""Run the bounded certificate, exceptional cases, and construction tests.

All tests use Python's standard library. Expanded rotations are generated in a
temporary directory and removed afterwards. Additional prime tests are regression
tests, not a substitute for the proof of the infinite family.
"""
from __future__ import annotations

import argparse
import hashlib
import json
from math import isqrt
from pathlib import Path
import subprocess
import sys
import tempfile

import kneser_constructor as constructor
import verify_bounded_permutation as bounded
from verify_exceptional import verify_all_exceptional, verify_base_certificate
from verify_expanded import verify as verify_expanded

HERE = Path(__file__).resolve().parent


def run(test_through: int = 179) -> dict:
    if test_through < 139:
        raise ValueError("test-through must be at least 139 to test both generic cases")
    finite = {"supplementary_interval": bounded.interval_certificate(),
              "boundary": [bounded.boundary_certificate(case) for case in (1, 2)]}
    if constructor.CANDIDATES != bounded.CHOICES:
        raise ValueError("Constructor and bounded-checker masks differ")
    # Compare with the separately implemented audit supplied in the constructor.
    constructor_audit = constructor.audit_boundary_lemma()
    for row, audit in zip(finite["boundary"], constructor_audit):
        if (row["case"], row["patterns"], row["sign_choices_tested"],
                row["transfer_choices_tested"]) != (
                audit["case"], audit["character_patterns"],
                audit["outside_choices_tested"], audit["transfer_choices_tested"]):
            raise ValueError("The two bounded verifiers disagree")
    exceptional = verify_all_exceptional()
    generic = []
    for h in range(131, test_through + 1, 8):
        if any(h % p == 0 for p in range(2, isqrt(h) + 1)):
            continue
        # A fresh process for large cases avoids retaining large Python allocators.
        if h > 179:
            result = subprocess.run(
                [sys.executable, str(Path(__file__).resolve()), "--one-prime", str(h)],
                check=True, capture_output=True, text=True)
            generic.append(json.loads(result.stdout))
        else:
            generic.append(check_one_prime(h))
    expanded = []
    with tempfile.TemporaryDirectory(prefix="bipartite_kneser_") as directory:
        for h in (11, 19):
            certificate = constructor.construct(h)
            model = constructor.AffineKneser(h, certificate["u"])
            output = Path(directory) / f"h{h}_full_rotation.json"
            constructor.write_expansion(model, certificate["cycle"], output)
            expanded.append(verify_expanded(output))
    names = ["kneser_constructor.py", "verify_bounded_permutation.py",
             "verify_exceptional.py", "verify_expanded.py", "verify_all.py",
             "exceptional_certificates.json"]
    hashes = {name: hashlib.sha256((HERE / name).read_bytes()).hexdigest() for name in names}
    return {"status": "passed", "source_sha256": hashes,
            "finite_certificate": finite,
            "exceptional_primes": exceptional,
            "generic_regression_tests": generic,
            "expanded_rotation_tests": expanded,
            "regression_test_limit": test_through}


def check_one_prime(h: int) -> dict:
    certificate = constructor.construct(h)
    report = verify_base_certificate(certificate)
    z = certificate["report"]["z"]
    q = (h - 1) // 2
    if not (9 <= z["ell"] <= q - 10 and z["ell"] % 2 == 1 and z["j"] >= 4):
        raise ValueError("The generic construction violates the manuscript's parameter bounds")
    report["A"], report["j"], report["upsilon"] = z["A"], z["j"], z["ell"]
    return report


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path, help="write the verification report")
    parser.add_argument("--test-through", type=int, default=179)
    parser.add_argument("--one-prime", type=int, help=argparse.SUPPRESS)
    args = parser.parse_args()
    try:
        result = check_one_prime(args.one_prime) if args.one_prime is not None else run(args.test_through)
        text = json.dumps(result, indent=2) + "\n"
        if args.output is not None:
            args.output.write_text(text, encoding="utf-8")
        print(text, end="")
    except (OSError, ValueError, KeyError, TypeError, AssertionError,
            subprocess.CalledProcessError) as error:
        parser.exit(1, f"verification failed: {error}\n")


if __name__ == "__main__":
    main()
