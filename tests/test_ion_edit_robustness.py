import copy
import json
import subprocess
import sys
import unittest
from collections import Counter

from scripts.probe_ion_coupling_certificates import CERTIFICATES
from scripts.probe_measured_ion_pentagon import load_fixture


class IonEditRobustnessTests(unittest.TestCase):
    def test_replays_integer_transport_and_distinct_minima(self):
        from scripts import probe_ion_edit_robustness as p
        expected = {"normal": (4690, 4690, 4790), "reverse": (4735, 4735, 4837)}
        out = p.experiment()
        for name, rec in load_fixture()["orders"].items():
            result = out["orders"][name]
            weights = [Counter() for _ in range(5)]
            totals = [0, 0, 0]
            for source, global_pair, global_bit, count in result["transport"]:
                copies = {v: set() for v in range(1, 6)}
                for i, (a, b) in enumerate(rec["ordered_edges"]):
                    x, y = (source >> (2*i)) % 2, (source >> (2*i+1)) % 2
                    weights[i][2*x+y] += count
                    copies[a].add(x)
                    copies[b].add(y)
                    def read(mask):
                        return (mask >> (a-1)) % 2, (mask >> (b-1)) % 2
                    totals[1] += count * ((x, y) != read(global_pair))
                    s, t = read(global_bit)
                    self.assertNotEqual((s, t), (1, 1))
                    totals[2] += count * ((x != s) + (y != t))
                totals[0] += count * any(len(vals) == 2 for vals in copies.values())
            self.assertEqual([[w[k] for k in range(4)] for w in weights], rec["counts"])
            self.assertEqual(tuple(totals), expected[name])
            keys = ("mismatched_stocks", "relabeled_pairs", "exclusive_bit_flips")
            for key, value, denominator in zip(keys, totals, (10000, 50000, 100000)):
                self.assertEqual(result["minima"][key]["count"], value)
                self.assertEqual(result["minima"][key]["denominator"], denominator)

    def test_corrupt_transports_do_not_verify(self):
        from scripts import probe_ion_edit_robustness as p
        rec = load_fixture()["orders"]["reverse"]
        cert = p.make_transport(rec["ordered_edges"], CERTIFICATES["reverse"]["lower"])
        for column, bad, diagnostic in ((0, 1024, "source"), (1, False, "target"),
                                        (2, 31, "exclusive"), (3, 0, "weight")):
            changed = [list(row) for row in cert]
            changed[0][column] = bad
            with self.assertRaisesRegex(ValueError, diagnostic):
                p.verify_order(rec, changed)
        changed = [list(row) for row in cert]
        changed[0][1] = 0
        with self.assertRaisesRegex(ValueError, "saturat"):
            p.verify_order(rec, changed)
        wrong = copy.deepcopy(rec)
        wrong["counts"][0][1] += 1
        wrong["counts"][0][2] -= 1
        with self.assertRaisesRegex(ValueError, "cells"):
            p.verify_order(wrong, cert)

    def test_low_unlike_marginal_obstruction_is_not_declared_zero_distance(self):
        from scripts import probe_ion_edit_robustness as p
        # Vertex 1 is always 1 on its outgoing edge, always 0 on its incoming edge.
        # U/T = 1 makes the unlike-count lower bound vacuous, not sharp.
        rec = load_fixture()["orders"]["normal"]
        rec["counts"] = [[0, 0, 10000, 0]] + [[10000, 0, 0, 0] for _ in range(4)]
        cert = p.make_transport(rec["ordered_edges"], [(1, 10000)])
        with self.assertRaisesRegex(ValueError, "mismatch: witness does not saturate"):
            p.verify_order(rec, cert)

    def test_cli_optimized(self):
        res = subprocess.run([sys.executable, "-O", "-B", "-m",
                              "scripts.probe_ion_edit_robustness", "--json"],
                             capture_output=True, text=True)
        self.assertEqual(res.returncode, 0, res.stderr)
        report = json.loads(res.stdout)
        self.assertIn("not a population", report["boundary"])
        self.assertIn("not observed", report["boundary"])
