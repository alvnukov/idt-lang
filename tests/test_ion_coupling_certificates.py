import json
import subprocess
import sys
import unittest
from fractions import Fraction as F

from scripts.probe_measured_ion_pentagon import load_fixture, score


class IonCouplingCertificatesTests(unittest.TestCase):
    def test_endpoints_and_interior_mixture_from_independent_bit_replay(self):
        from scripts import probe_ion_coupling_certificates as p
        expected = {"normal": (F(469, 1000), F(4479, 1000)),
                    "reverse": (F(947, 2000), F(44837, 10000))}
        for order, rec in load_fixture()["orders"].items():
            lo, hi = expected[order]
            for t in (F(0), F(3, 7), F(1)):
                cells = [[0]*4 for _ in range(5)]
                total = objective = 0
                for key, coeff in (("lower", 1-t), ("upper", t)):
                    atoms = p.CERTIFICATES[order][key]
                    self.assertEqual(len(atoms), 16)
                    for mask, ticks in atoms:
                        weight = coeff * ticks / 10000
                        self.assertGreaterEqual(weight, 0)
                        total += weight
                        copies = {v: [] for v in range(1, 6)}
                        for i, (a, b) in enumerate(rec["ordered_edges"]):
                            x, y = (mask >> (2*i)) & 1, (mask >> (2*i+1)) & 1
                            cells[i][2*x+y] += weight
                            copies[a].append(x)
                            copies[b].append(y)
                        objective += weight * sum(x != y for x, y in copies.values())
                self.assertEqual(total, 1)
                self.assertEqual([[10000*x for x in row] for row in cells], rec["counts"])
                self.assertEqual(objective, (1-t)*lo + t*hi)

    def test_compact_cli_optimized_python_reports_unequal_floors(self):
        proc = subprocess.run([sys.executable, "-B", "-O", "-m",
                               "scripts.probe_ion_coupling_certificates", "--json"],
                              capture_output=True, text=True)
        self.assertEqual(proc.returncode, 0, proc.stderr)
        report = json.loads(proc.stdout)
        for order, step, hi in (("normal", 1, "4479/1000"), ("reverse", -1, "44837/10000")):
            row = report["orders"][order]
            ref = score(load_fixture()["orders"][order]["counts"], step)
            self.assertEqual(row["E_D_interval"], [ref["conditional_D_floor"], hi])
            self.assertEqual(row["marginal_TV_sum"], ref["marginal_TV_sum"])
            self.assertEqual(row["assignments_checked"], 1024)
        self.assertEqual(report["orders"]["normal"]["marginal_TV_sum"], "23/250")
        self.assertIn("not measured physical disturbance", report["boundary"])
        self.assertIn("not a population confidence interval", report["boundary"])

    def test_rejects_transposed_row_and_missing_cell(self):
        from scripts import probe_ion_coupling_certificates as p
        for corrupt in (lambda r: [r[0], r[2], r[1], r[3]], lambda r: r[:3]):
            rec = load_fixture()["orders"]["normal"]
            rec["counts"][2] = corrupt(rec["counts"][2])
            with self.assertRaises(ValueError):
                p.verify_order(rec, p.CERTIFICATES["normal"])

    def test_rejects_weight_shift_and_out_of_range_mask(self):
        from scripts import probe_ion_coupling_certificates as p
        rec = load_fixture()["orders"]["reverse"]
        original = p.CERTIFICATES["reverse"]
        (a, x), (b, y), *tail = original["upper"]
        for head in ([(a, x+1), (b, y-1)], [(1024+a, x), (b, y)],
                     [(a, -1), (b, x+y+1)], [(a, x), (b, y+1)]):
            with self.assertRaises(ValueError):
                p.verify_order(rec, dict(original, upper=head+tail))

    def test_refuses_to_call_unsaturated_bounds_endpoints(self):
        from scripts import probe_ion_coupling_certificates as p
        # All ten bits bright: only D=0 is possible; D <= 2S=10 is not sharp.
        rec = load_fixture()["orders"]["normal"]
        rec["counts"] = [[0, 0, 0, 10000] for _ in range(5)]
        law = [(1023, 10000)]
        with self.assertRaisesRegex(ValueError, "saturat"):
            p.verify_order(rec, {"lower": law, "upper": law})
