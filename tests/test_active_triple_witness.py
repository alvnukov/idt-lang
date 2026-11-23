"""Regression checks for the finite active-sector third-order witness."""

import importlib
import unittest
from fractions import Fraction


class ActiveTripleWitnessTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        name = "scripts.probe_active_triple_witness"
        if importlib.util.find_spec(name) is None:
            raise AssertionError("active triple witness is not implemented")
        cls.result = importlib.import_module(name).certificate()

    def test_exhaustive_raw_marginals(self):
        self.assertEqual(self.result["subsets_checked"], (32, 496, 4960))
        self.assertEqual(self.result["mismatches"], (0, 0, 0))
        self.assertEqual(self.result["fourth_order_mismatches"], 128)

    def test_supported_preparations_in_two_active_recurrent_components(self):
        self.assertEqual(self.result["component_sizes"], (2944, 2944))
        self.assertEqual(self.result["active_region_size"], 5888)

    def test_unconditioned_next_step_short_pair_differs(self):
        self.assertEqual(self.result["next_pair"], (Fraction(1, 32), Fraction(1, 96)))

    def test_one_offer_sector_has_an_exact_third_order_decoder(self):
        from scripts import probe_active_triple_witness as w

        p = w.Ports.from_graph(w.cycle_square(16))
        seed = w.fixture(16, 0, 1)[0] | w.fixture(16, 8, 1)[0]
        region = w.recurrent_component(p, seed) | w.recurrent_component(p, w.transform(seed, 1))
        remaining = {s for s in region if len(w.offers(p, s)) == 1}
        self.assertEqual(len(remaining), 3008)
        s0, s3, s4 = (w.link(k, k + 1) for k in (0, 3, 4))
        l3, l4, l5 = (w.link(k, k + 2) for k in (3, 4, 5))
        rates = []
        while remaining:
            stamp = next(iter(remaining))
            orbit = {w.transform(stamp, k, h) for k in range(16) for h in (-1, 1)}
            self.assertTrue(orbit <= remaining)
            remaining -= orbit
            def count(*bonds):
                return sum(set(bonds) <= s for s in orbit)
            predicted = count(s0, s3) + 2 * (
                count(s0, s4, l5) + count(s0, s4, l4) - count(s0, s3, l4) - count(s0, s3, l3)
            )
            actual = sum({s0, s3} <= next(iter(w.offers(p, s))).apply(s) for s in orbit)
            self.assertEqual(predicted, actual)
            rates.append(Fraction(actual, len(orbit)))
        self.assertEqual(sorted(rates), [Fraction(0)] * 84 + [Fraction(1, 16)] * 10)
