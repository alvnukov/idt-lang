from __future__ import annotations

import unittest
from collections import Counter
from fractions import Fraction as F
from itertools import product

from scripts import probe_finite_detector_identity as rates
from scripts import probe_native_qutrit_frames as frames
from scripts import probe_native_row_probability as row
from scripts import probe_unread_row_duplication as dup
from scripts.gaussian_dyadic_words import ONE, ZERO, g


class NativeFrameControls(unittest.TestCase):
    def test_tree_is_connected_and_singly_counted(self) -> None:
        bases, values = frames.tree(3)
        pending = dict.fromkeys(bases)
        reached = {next(iter(values))}
        while pending:
            attached = [b for b in pending if any(v in reached for v in b)]
            self.assertTrue(attached)
            for b in attached:
                reached.update(b)
                del pending[b]
        self.assertEqual(reached, set(values))
        self.assertEqual(3 * len(bases), len(reached) + len(bases) - 1)
        self.assertEqual({sum(values[v] for v in b) for b in bases}, {1})

    def test_four_modes_and_blank_port_do_not_test_the_same_class(self) -> None:
        rays, contexts = frames.parity_four()
        uses = Counter(rays[i] for b in contexts for i in b)
        self.assertEqual(len(uses), 18)
        self.assertEqual(set(uses.values()), {2})
        self.assertEqual(len(contexts) % 2, 1)
        self.assertEqual(sum(frames.blank_port_pentagon()), F(33, 16))

    def test_balance_holds_entrywise_not_just_for_calibrated_states(self) -> None:
        rows = (rates.TARGET, rates.Z0, rates.Z1, rates.XPLUS, rates.YPLUS)
        for j, k in product(range(2), repeat=2):
            self.assertEqual(
                sum(
                    (
                        g(c) * r[j].star() * r[k]
                        for r, c in zip(rows, rates.COEFF, strict=True)
                    ),
                    ZERO,
                ),
                ZERO,
            )
        left, right = rates.tests()
        self.assertEqual(left[-2:], right[-2:])
        self.assertEqual(row.gram(left, 2), ((ONE, ZERO), (ZERO, ONE)))
        self.assertEqual(row.gram(left, 2), row.gram(right, 2))

    def test_uncertainty_may_make_a_quartic_excess_inconclusive(self) -> None:
        values = (F(13, 16) + F(221, 1392), F(1), F(0), F(1, 2), F(1, 2))
        points = tuple((v, v) for v in values)
        zero = (F(0),) * 8
        self.assertEqual(rates.residual_range(points), (F(221, 1392),) * 2)
        self.assertEqual(
            rates.diagnostic(points, zero, (F(0), F(0))),
            "excluded_under_supplied_bounds",
        )
        self.assertEqual(
            rates.diagnostic(points, zero, (F(221, 1392), F(0))), "inconclusive"
        )
        with self.assertRaises(ValueError):
            rates.diagnostic(points, (), ())
        with self.assertRaises(ValueError):
            rates.residual_range(((F(1), F(0)),) + points[1:])

    def test_duplication_is_an_isometry_not_two_independent_copies(self) -> None:
        for d in (1, 2, 3):
            a, b = dup.example(d)
            self.assertEqual(a[0], b[0])
            ab = dup.duplicate(a, b)
            self.assertEqual(ab[0], ab[len(a)])
            self.assertEqual(row.gram(ab, d), row.gram(a, d))
            self.assertEqual(row.gram(ab[: len(a)], d)[0][0] * g(2), ONE)
