import unittest
from fractions import Fraction

from scripts.check_triangle_null_trials import null_report, population_controls


class TriangleNullTests(unittest.TestCase):
    def test_conditional_and_bad_seed_controls(self):
        population_controls()

    def test_direction_and_missing_attempts(self):
        self.assertEqual(null_report(10, 10, 10)["upper_tail"], "1/1024")
        self.assertEqual(null_report(10, 10, 0)["upper_tail"], "1")
        self.assertEqual(null_report(10, 10, 9)["upper_tail"], "11/1024")
        self.assertEqual(null_report(10, 9, 9)["status"], "inconclusive_missing_score")
        self.assertIsNone(null_report(20, 0, 0)["upper_tail"])

    def test_exhaustive_small_calibration(self):
        from math import comb

        for n in range(1, 14):
            tails = [Fraction(null_report(n, n, k)["upper_tail"]) for k in range(n+1)]
            self.assertEqual([a-b for a, b in zip(tails, [*tails[1:], 0], strict=True)],
                             [Fraction(comb(n, k), 2**n) for k in range(n+1)])

    def test_input_limits(self):
        for args in ((False, 0, 0), (1, 1, 1.0), (0, 0, 0), (2, 1, 2),
                     (4097, 0, 0), (1, 2, 0), (1, 0, -1)):
            with self.assertRaises(ValueError):
                null_report(*args)
