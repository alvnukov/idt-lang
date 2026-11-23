import json
from itertools import product
from math import sqrt
import subprocess
import sys
import unittest


class NativePentagonTests(unittest.TestCase):
    def test_module_runs_without_asserts(self):
        run = subprocess.run(
            [sys.executable, "-B", "-O", "-m", "scripts.probe_native_pentagon_contexts", "--json"],
            capture_output=True, text=True, check=False,
        )
        self.assertEqual(run.returncode, 0, run.stderr)
        result = json.loads(run.stdout)
        self.assertEqual(result["native"]["score_histogram_over_24"], {"1": 8, "2": 16})
        self.assertEqual(result["potential_assignments"], 1024)
        self.assertEqual(result["single_frame"]["faithful_cycles_exist"], False)

    def test_sequential_pairs_on_one_stock_agree_with_independent_xor_routing(self):
        from scripts import probe_native_pentagon_contexts as p
        for source, bits in p.STOCKS:
            expected = []
            for hubs, port in p.EVENTS:
                loc = source
                for i, j in hubs:
                    if bits[i] != bits[j] and loc in (i, j):
                        loc = j if loc == i else i
                expected.append(int(loc == port))
            for i, j in product(range(5), repeat=2):
                self.assertEqual(p.read_pair((source, bits), i, j), (expected[i], expected[j]))
        self.assertEqual(len(set(p.EVENTS)), 5)

    def test_routing_closure_distinguishes_single_and_restored_instruments(self):
        from scripts import probe_native_pentagon_contexts as p
        frame = p.frame_closure()
        self.assertEqual((frame["maps"], frame["events"]), (108, 81))
        self.assertEqual((frame["coframe_pairs"], frame["all_disjoint_pairs"]), (324, 648))
        witness = p.native_witness()
        self.assertEqual(witness["exclusive_edges"], 5)
        self.assertEqual(witness["co_clickable_diagonals"], 5)
        self.assertEqual(witness["symmetric_stock_count"], 5)
        self.assertEqual(witness["symmetric_hits_per_event"], [2] * 5)

    def test_sharp_bound_sees_defects_not_just_equal_marginals(self):
        from scripts import probe_native_pentagon_contexts as p
        vals = {p.score(bits[:5], bits[5:]) for bits in product((0, 1), repeat=10)}
        self.assertTrue(all(s <= 2 + d / 2 + j for s, d, j in vals))
        self.assertTrue({(2, 0, 0), (2.5, 1, 0), (3, 0, 1)} <= vals)
        low = p.edge_controls(alternating=True)
        high = p.edge_controls(alternating=False)
        self.assertEqual(low["edge_counts"], high["edge_counts"])
        self.assertEqual(low["edge_counts"], [[0, 5, 5, 0]] * 5)
        self.assertEqual((low["mean_D"], high["mean_D"]), (1, 5))

    def test_external_axial_target_is_not_a_native_score(self):
        from scripts import probe_native_pentagon_contexts as p
        result = p.external_target()
        self.assertAlmostEqual(result["score"], sqrt(5))
        self.assertLess(result["max_adjacent_abs_dot"], 1e-14)
        w = result["contextual_mixture_weight"]
        self.assertAlmostEqual((1-w) * 0.4 + w * 0.5, 1/sqrt(5))
        self.assertAlmostEqual(w, 2 * (result["score"] - 2))

    def test_different_couplings_have_the_same_five_complete_target_tables(self):
        from scripts import probe_native_pentagon_contexts as p
        result = p.verify()
        self.assertIn("target_couplings", result)
        couplings = result["target_couplings"]
        w = 2*sqrt(5)-4
        self.assertAlmostEqual(couplings["minimum_mean_D"], w)
        self.assertAlmostEqual(couplings["alternative_mean_D"], 5*w)
        for row in couplings["five_edge_probabilities_00_01_10_11"]:
            for got, expected in zip(row, (1-2/sqrt(5), 1/sqrt(5), 1/sqrt(5), 0), strict=True):
                self.assertAlmostEqual(got, expected)
