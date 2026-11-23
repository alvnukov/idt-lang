from fractions import Fraction as F
from itertools import product
import unittest

from scripts import probe_vacuum_compensated_network as n


class VacuumCompensatedNetworkTests(unittest.TestCase):
    def test_all_operating_states_and_law(self):
        n_fixed = 0
        for d, e, f, g in product((1, 2, 3), repeat=4):
            raw = ((d, e), (f, g))
            out = n.device(raw, "U")
            self.assertEqual(sum(pair.count(3) for pair in raw), sum(pair.count(3) for pair in out))
            n_fixed += n.device(out, "U") == raw
            if 3 not in (d, e, f, g):
                self.assertEqual(n.device(raw, "S"), ((3-d, e), (3-f, g)))
                self.assertEqual(out, raw)
            elif sorted((d, f)) == [1, 3] and max(e, g) <= 2:
                expected = ((f, e), (d, g)) if e != g else raw
                self.assertEqual(out, expected)
        self.assertEqual(n_fixed, 63)

    def test_common_stock_crossing_coefficients(self):
        self.assertEqual(n.crossing_kernel(), ((0, 2), (1, 0)))

    def test_chained_raw_programs(self):
        target = ((4, 2, 2), (4, 2, 2), (0, 4, 4))
        self.assertEqual(n.counts("S", n.CHAIN), ((4, 3, 1), (4, 3, 1), (0, 2, 6)))
        self.assertEqual(n.counts("F", n.CHAIN), ((4, 3, 1), (4, 3, 1), (0, 4, 4)))
        self.assertEqual(n.counts("U", n.CHAIN), target)

    def test_cycle_and_repeated_edge_controls(self):
        triangle = ((2, 2, 4), (4, 2, 2), (2, 4, 2))
        repeated = ((6, 0, 2), (0, 6, 2), (2, 2, 4))
        self.assertEqual(n.counts("U", n.TRIANGLE), triangle)
        self.assertEqual(n.fresh_counts(n.TRIANGLE), ((3, 2, 3), (3, 2, 3), (2, 4, 2)))
        self.assertEqual(n.coherent_triangle(), tuple(tuple(F(x, 8) for x in row) for row in triangle))
        self.assertEqual(n.counts("U", n.REPEATED), repeated)
        self.assertEqual(n.sole_overlap(repeated), ((0, 1, 2),))

    def test_complete_run_includes_two_arm_controls(self):
        evidence = n.verify()
        self.assertEqual(evidence["two_arm"], {"rows": 32, "launches": 512, "pinned_erases": 256})
        self.assertEqual(evidence["forest_chain_multiplicities"], (2, 2, 2, 2))


if __name__ == "__main__":
    unittest.main()
