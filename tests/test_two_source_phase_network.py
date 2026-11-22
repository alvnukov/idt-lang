from __future__ import annotations

import unittest
from fractions import Fraction as F
from itertools import product

from scripts import probe_balanced_phase_composition as comp
from scripts import probe_phase_network_game as game
from scripts import probe_three_axis_source_parity as parity
from scripts import probe_two_source_phase_network as net
from scripts.gaussian_dyadic_words import g


class TwoSourceControls(unittest.TestCase):
    def test_three_axis_import_is_a_process_calibration(self) -> None:
        p = parity.triple_product(parity.REAL_AXES)
        self.assertEqual(parity.multiply(p, p), parity.scale(-1, parity.eye(4)))
        self.assertEqual(parity.symmetric(p), parity.scale(0, parity.eye(4)))
        # Phase-blind return of a whole state is identical for p² and +I.
        self.assertNotEqual(parity.multiply(p, p), parity.eye(4))
        self.assertEqual(parity.real_sharp_control(), 2)
        self.assertEqual(parity.complex_native_control(), 3)

    def test_balanced_filter_is_not_ordinary_real_composition(self) -> None:
        rho = comp.matrix(((F(1, 3), F(1, 6)), (F(1, 6), F(2, 3))))
        real_product = comp.tensor(rho, rho)
        self.assertEqual(comp.trace(comp.multiply(real_product, comp.K)), 0)
        self.assertEqual(comp.trace(comp.multiply(real_product, comp.P_MINUS)), F(1, 2))
        self.assertEqual(comp.trace(comp.multiply(comp.OMEGA_MINUS, comp.P_MINUS)), 1)

    def test_all_settings_but_not_all_scores_are_active(self) -> None:
        table = {
            (x, z): {out: F(1, 16) for out in product((-1, 1), (0, 1), (0, 1), (-1, 1))}
            for x, z in product(range(3), range(6))
        }
        self.assertEqual(net.functional(table), 0)
        self.assertEqual(game.masses(table), {-1: F(1, 3), 0: F(1, 3), 1: F(1, 3)})
        del table[0, 5]
        with self.assertRaises((ValueError, ArithmeticError, AssertionError)):
            game.masses(table)

    def test_network_ideal_is_not_a_replay_of_observed_data(self) -> None:
        base = net.analyzer((g(F(3, 4), F(1, 2)), g(F(1, 4), F(1, 4)), g(F(1, 4))))
        dist = net.distributions(base)
        self.assertEqual(game.masses(dist)[1], F(53, 96))
        self.assertEqual(net.functional(dist) - net.BOUND, F(429, 2000))
        self.assertEqual(game.eligibility(frozenset(), game.Bet())[0], False)

    def test_order_must_not_be_reconstructed_from_setting_counts(self) -> None:
        bet = game.Bet()
        threshold = bet.factor(1)
        a = game.accumulate((1, 0, -1), bet, threshold)
        b = game.accumulate((-1, 0, 1), bet, threshold)
        self.assertEqual(a.final, b.final)
        self.assertEqual(a.first_crossing, 1)
        self.assertIsNone(b.first_crossing)
        self.assertFalse(
            game.Bet(contamination=(F(63, 8) - net.BOUND) / (12 - net.BOUND)).betting
        )
