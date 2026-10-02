"""Regression tests for certificate replay, validation, and manuscript conventions."""
from __future__ import annotations

from copy import deepcopy
import json
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest
from unittest.mock import patch

import kneser_constructor as constructor
import verify_bounded_permutation as bounded
from verify_exceptional import load_records, verify_base_certificate
from verify_expanded import verify as verify_expanded

HERE = Path(__file__).resolve().parent


class CertificateTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.records = load_records()

    def test_all_seven_records(self):
        for h in (11, 19, 43, 59, 67, 83, 107):
            with self.subTest(h=h):
                report = verify_base_certificate(
                    constructor.construct_from_record(self.records[str(h)]))
                self.assertTrue(report['single_cycle'])
                self.assertEqual(report['Q1_checked'], (h-2)*(h-3)//2)
                self.assertEqual(report['Q1_checked'], report['Q2_checked'])

    def test_replay_does_not_search(self):
        with patch.object(constructor, 'choose_z', side_effect=AssertionError('parameter search')), \
             patch.object(constructor, 'transfer_dp', side_effect=AssertionError('transfer search')):
            for h in (43, 59, 67, 83, 107):
                verify_base_certificate(constructor.construct_from_record(self.records[str(h)]))

    def test_reject_changed_parameters(self):
        for field, value in [('A', 1), ('j', 3), ('upsilon', 11), ('u', 1)]:
            with self.subTest(field=field):
                record = deepcopy(self.records['43'])
                record[field] = value
                with self.assertRaises(ValueError):
                    constructor.construct_from_record(record)

    def test_reject_out_of_range_masks(self):
        for field, value in [('outside_mask', 1 << 12), ('interval_mask', 1 << 8),
                             ('outside_mask', -1), ('interval_mask', True)]:
            with self.subTest(field=field, value=value):
                record = deepcopy(self.records['43'])
                record[field] = value
                with self.assertRaises(ValueError):
                    constructor.construct_from_record(record)

    def test_reject_wrong_interval_maps(self):
        record = deepcopy(self.records['43'])
        record['forward_interval_maps'] = ['201', '102']  # inverse, not forward
        with self.assertRaises(ValueError):
            constructor.construct_from_record(record)

    def test_reject_changed_interval_switch(self):
        record = deepcopy(self.records['43'])
        record['interval_mask'] ^= 1
        with self.assertRaises(ValueError):
            constructor.construct_from_record(record)

    def test_reject_duplicate_base_label(self):
        record = deepcopy(self.records['11'])
        record['base_cycle'][1] = record['base_cycle'][0]
        with self.assertRaises(ValueError):
            constructor.construct_from_record(record)

    def test_independent_verifier_rejects_bad_order(self):
        certificate = deepcopy(constructor.construct(11))
        certificate['cycle'][0], certificate['cycle'][1] = (
            certificate['cycle'][1], certificate['cycle'][0])
        with self.assertRaises(ValueError):
            verify_base_certificate(certificate)

    def test_independent_verifier_rejects_noninteger_label(self):
        certificate = deepcopy(constructor.construct(11))
        certificate['cycle'] = [list(s) for s in certificate['cycle']]
        certificate['cycle'][0][0] = 2.0
        with self.assertRaises(ValueError):
            verify_base_certificate(certificate)

    def test_reject_missing_prime(self):
        records = deepcopy(self.records)
        del records['107']
        with tempfile.TemporaryDirectory() as directory:
            path = Path(directory) / 'bad.json'
            path.write_text(json.dumps(records), encoding='utf-8')
            with self.assertRaises(ValueError):
                load_records(path)

    def test_invalid_input_primes(self):
        for h in (3, 7, 27, 43*43):
            with self.subTest(h=h), self.assertRaises(ValueError):
                constructor.construct(h)

    def test_generic_parameter_bounds(self):
        for h in (131, 139, 163, 179):
            with self.subTest(h=h):
                certificate = constructor.construct(h)
                z = certificate['report']['z']
                self.assertGreaterEqual(z['j'], 4)
                self.assertTrue(9 <= z['ell'] <= (h-1)//2-10)
                verify_base_certificate(certificate)

    def test_translation_order_matches_manuscript(self):
        for h in (43, 131):
            certificate = constructor.construct(h)
            cycle = certificate['cycle']
            rho = {s: cycle[(i+1) % len(cycle)] for i, s in enumerate(cycle)}
            M = (h-3)//8
            ell = M+1 if h % 3 == 1 else 5
            # The first quadruple at index ell+1 goes to index ell-1.
            self.assertEqual(rho[(ell+2, 0)], (ell, 0))

    def test_splice_endpoints_and_coverage(self):
        for h in (43, 59, 131, 139):
            certificate = constructor.construct(h)
            model = constructor.AffineKneser(h, certificate['u'])
            cycle = certificate['cycle']
            rho = {s: cycle[(i+1) % len(cycle)] for i, s in enumerate(cycle)}
            z = certificate['report']['z']
            E, q = z['E'], model.q
            w0 = 1 if h % 3 == 1 else q-2
            a, b = model.logs[z['A']], model.logs[z['B']]

            def interior(start, target):
                path = []
                x = rho[start]
                while x != target:
                    self.assertLess(len(path), len(cycle))
                    path.append(x)
                    x = rho[x]
                return path

            self.assertEqual(rho[model.X(E, q-1)], model.X(E, -w0))
            self.assertEqual(rho[model.X(E, -(q-1))], model.X(E, w0))
            paths = (interior(model.X(-E, -(q-1)), model.X(-E, w0))
                     + interior(model.X(-E, q-1), model.X(-E, -w0)))
            translations = {s for s in model.S if s[1] == 0}
            self.assertEqual(set(paths), translations)
            self.assertEqual(len(paths), len(translations))
            self.assertEqual(rho[model.X(a, 1)], model.X(b, -1))
            self.assertEqual(rho[model.X(a, -1)], model.X(b, 1))
            paths = (interior(model.X(-a, -1), model.X(-b, -1))
                     + interior(model.X(-a, 1), model.X(-b, 1)))
            zeros = {model.X(k, 0) for k in range(1, q)}
            self.assertEqual(set(paths), zeros)
            self.assertEqual(len(paths), len(zeros))

    def test_bounded_checker_rejects_empty_mask_list(self):
        with patch.dict(bounded.CHOICES, {1: []}):
            with self.assertRaises(AssertionError):
                bounded.boundary_certificate(1)

    def test_optimized_python_is_rejected(self):
        for filename in ('kneser_constructor.py', 'verify_bounded_permutation.py',
                         'verify_exceptional.py', 'verify_all.py'):
            with self.subTest(filename=filename):
                result = subprocess.run([sys.executable, '-O', str(HERE / filename), '--help'],
                                        capture_output=True, text=True)
                self.assertNotEqual(result.returncode, 0)
                self.assertIn('without -O', result.stderr)

    def test_default_data_path_outside_working_directory(self):
        with tempfile.TemporaryDirectory() as directory:
            result = subprocess.run([sys.executable, str(HERE / 'verify_exceptional.py')],
                                    cwd=directory, capture_output=True, text=True)
            self.assertEqual(result.returncode, 0, result.stderr)
            self.assertEqual(len(json.loads(result.stdout)['exceptional_primes']), 7)

    def test_expanded_verifier_rejects_bad_rotation(self):
        certificate = constructor.construct(11)
        model = constructor.AffineKneser(11, certificate['u'])
        with tempfile.TemporaryDirectory() as directory:
            output = Path(directory) / 'full.json'
            constructor.write_expansion(model, certificate['cycle'], output)
            obj = json.loads(output.read_text())
            obj['rotations'][0][0] = 0
            output.write_text(json.dumps(obj), encoding='utf-8')
            with self.assertRaises(ValueError):
                verify_expanded(output)


if __name__ == '__main__':
    unittest.main(verbosity=2)
