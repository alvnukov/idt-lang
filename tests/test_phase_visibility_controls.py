import unittest
from fractions import Fraction as F
from itertools import product

from scripts import probe_phase_visibility_controls as probe


class PhaseVisibilityTests(unittest.TestCase):
    def test_binary_and_trit_boundary_on_each_external_cell(self):
        for x, y in product(range(8), repeat=2):
            d = min((x-y) % 8, (y-x) % 8)
            for c, observed in [(F(1, 2), probe.binary_jitter(x, y)),
                                (F(5, 8), probe.trit_boundary(x, y))]:
                # V=c*sqrt(2); odd target probabilities are rational.
                expected = [(F(1, 2), c/2), ((1+c)/2, 0), (F(1, 2), 0),
                            ((1-c)/2, 0), (F(1, 2), -c/2)][d]
                self.assertEqual(observed, expected)

    def test_exact_third_harmonic_and_failure_of_equal_jitter(self):
        self.assertEqual(probe.triangle_cosine_coefficient(1), (F(1, 4), F(1, 8)))
        self.assertEqual(probe.triangle_cosine_coefficient(3), (F(1, 4), F(-1, 8)))
        self.assertNotEqual(probe.binary_jitter(0, 0, center=(F(1, 3), 0)),
                            probe.binary_jitter(0, 0))

    def test_trit_parity_scramble_leaves_odd_pairs_unchanged(self):
        for x, y in product(range(8), repeat=2):
            plain, scrambled = probe.trit_modes(x, y)
            if (x-y) % 2:
                self.assertEqual(scrambled, plain)
            else:
                self.assertEqual(scrambled, F(1, 2))

    def test_curvature_all_launches_and_symmetric_allowances(self):
        triangle = {0: (100, 0, 100), 1: (75, 25, 100), 2: (50, 50, 100)}
        self.assertEqual(probe.curvature_interval(triangle), (0, 0))
        # Synthetic stress vector, not experimental data or fitted evidence.
        curve = {0: (90, 10, 100), 1: (82, 18, 100), 2: (50, 50, 100)}
        self.assertEqual(probe.curvature_interval(curve), (F(6, 25), F(6, 25)))
        self.assertEqual(probe.curvature_interval(curve, allowance=F(3, 50)),
                         (0, F(12, 25)))
        # 30 unclassified launches at the middle cell admit zero curvature.
        curve[1] = (60, 10, 100)
        self.assertLessEqual(probe.curvature_interval(curve)[0], 0)
        del curve[1]
        self.assertEqual(probe.curvature_interval(curve), (F(-7, 5), F(3, 5)))

    def test_invalid_counts_and_allowances(self):
        for row in [(1, 2, 2), (-1, 0, 2), (True, 0, 1)]:
            with self.assertRaises(ValueError):
                probe.curvature_interval({0: row})
        with self.assertRaises(ValueError):
            probe.curvature_interval({}, allowance=-1)

    def test_misaligned_ramp_can_fake_positive_curvature(self):
        # Middle knob really at 3/4 of a grid step rather than 1; the static
        # triangle then gives 13/16 rather than 12/16. No physical observations.
        shifted = {0: (16, 0, 16), 1: (13, 3, 16), 2: (8, 8, 16)}
        self.assertEqual(probe.curvature_interval(shifted), (F(1, 8), F(1, 8)))
        low, high = probe.curvature_interval(shifted, allowance=F(1, 16))
        self.assertLessEqual(low, 0)
        self.assertGreaterEqual(high, 0)

    def test_static_ramp_bowed_other_way_and_no_launches(self):
        opposite = {0: (16, 0, 16), 1: (11, 5, 16), 2: (8, 8, 16)}
        self.assertEqual(probe.curvature_interval(opposite), (F(-1, 8), F(-1, 8)))
        self.assertEqual(probe.curvature_interval({0: (0, 0, 0)}), (-2, 2))


if __name__ == "__main__":
    unittest.main()
