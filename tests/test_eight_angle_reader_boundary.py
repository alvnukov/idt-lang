"""Finite reader contracts, not evidence that native contacts produce eight phases."""

import unittest
from fractions import Fraction as F
from importlib.util import find_spec
from itertools import product
from math import cos, pi, sqrt


class EightAngleReaderTests(unittest.TestCase):
    def setUp(self):
        self.assertIsNotNone(find_spec("scripts.probe_eight_angle_reader_boundary"),
                             "the finite eight-setting comparator certificate is missing")
        from scripts import probe_eight_angle_reader_boundary
        self.p = probe_eight_angle_reader_boundary

    def test_four_cell_witness_and_triangle_sharp_on_complete_grid(self):
        p = self.p
        self.assertEqual(p.chsh_deterministic_scores(), (1, 3))
        for x, y in product(range(8), repeat=2):
            d = min((x-y) % 8, (y-x) % 8)
            near = p.triangle_probability(x, y)
            self.assertEqual(near, 1 - F(d, 4))
            target = cos(pi * (x-y) / 8)**2
            self.assertAlmostEqual(abs(target - near), (sqrt(2)-1)/4 if d % 2 else 0)

    def test_unrestricted_fusion_capacities_without_endpoint_assumptions(self):
        # A column of a binary-left fusion table has just 4 possible truth functions.
        for sizes, wins in [((1, 4), 8), ((2, 4), 12), ((3, 3), 13),
                            ((3, 4), 14), ((4, 4), 16)]:
            with self.subTest(sizes=sizes):
                self.assertEqual(self.p.block_cap(*sizes), wins)

    def test_trit_optimum_attained_on_every_cell(self):
        for x, y in product(range(8), repeat=2):
            d = min((x-y) % 8, (y-x) % 8)
            self.assertEqual(self.p.trit_probability(x, y),
                             (1, F(13, 16), F(1, 2), F(3, 16), 0)[d])

    def test_fixed_three_by_four_fusion_exact_as_affine_surd(self):
        for x, y in product(range(8), repeat=2):
            d = min((x-y) % 8, (y-x) % 8)
            left, right = self.p.mixed_coefficients(x, y)
            self.assertEqual((left, right),
                             [(1, 0), (F(1, 2), F(1, 4)), (F(1, 2), 0),
                              (F(1, 2), F(-1, 4)), (0, 0)][d])
            self.assertAlmostEqual(left + sqrt(2) * right, cos(pi*(x-y)/8)**2)

    def test_finite_equiprobable_stock_approximates_without_attaining_irrational_cell(self):
        for n in (1, 3, 16, 31):
            m = round(n * 2*(sqrt(2)-1))
            for x, y in product(range(8), repeat=2):
                value = self.p.finite_probability(x, y, m, n)
                self.assertIsInstance(value, F)
                self.assertEqual((8*n) % value.denominator, 0)
                self.assertLessEqual(abs(value - cos(pi*(x-y)/8)**2), 1/(16*n))

    def test_incomplete_observations_use_every_launched_trial(self):
        p = self.p
        # On each positive cell 8 D0, no D1; on the negative cell 0 D0, 8 D1.
        # Two further launches unassigned at every setting: lower score 3.2, not 4.
        counts = {pair: ((8, 0, 10) if win else (0, 8, 10)) for pair, win in p.FOUR_CELLS}
        self.assertEqual(p.lower_wins(p.FOUR_CELLS, counts), F(16, 5))
        self.assertEqual(p.lower_wins(p.FOUR_CELLS, counts, calibration=F(1, 20)), 3)
        del counts[(0, 7)]
        self.assertEqual(p.lower_wins(p.FOUR_CELLS, counts), F(12, 5))
        counts[(0, 7)] = (6, 5, 10)
        with self.assertRaises(ValueError):
            p.lower_wins(p.FOUR_CELLS, counts)

    def test_even_even_restriction_is_an_actual_raw_four_phase_replay(self):
        self.assertEqual(self.p.native_even_check(), 128)
