from __future__ import annotations

import unittest
from fractions import Fraction as F

from scripts import probe_native_qutrit_frames as native
from scripts import probe_native_rational_pentagon as pent
from scripts import probe_qutrit_residue_frames as residue
from scripts.gaussian_dyadic_words import ONE, ZERO, g


class QutritExtensionControls(unittest.TestCase):
    def test_projector_exists_when_normalizing_column_has_inert_norm(self) -> None:
        v = (g(-1), g(-1), ONE)
        p = pent.projector(v)
        self.assertEqual(pent.multiply(p, p), p)
        self.assertEqual(p[0][0], g(F(1, 3)))
        self.assertFalse(pent.gaussian_norm_integer(3))
        self.assertTrue(pent.gaussian_norm_integer(9))

    def test_rational_sharp_context_not_a_naked_basis_change(self) -> None:
        p = pent.projector((g(-1), g(-1), ONE))
        q = pent.projector((ONE, ZERO, ONE))
        self.assertEqual(pent.multiply(p, q), pent.scale(p, ZERO))
        psi = (g(F(1, 2), -F(1, 2)), g(F(1, 2), -F(1, 2)), ZERO)
        self.assertEqual(pent.probability(p, psi), F(2, 3))
        self.assertEqual(pent.probability(q, psi), F(1, 4))

    def test_mod_three_unsat_does_not_lift_to_native_rays(self) -> None:
        frames = residue.enumerate_frames(3)
        witness, _, _ = residue.valuation_search(frames)
        self.assertIsNone(witness)
        self.assertEqual(residue.native_orbit(frames), (63, 63))
        self.assertEqual(residue.distinct_five_cycles(frames), 0)
        bases, color = native.tree(3)
        self.assertTrue(all(sum(color[v] for v in b) == 1 for b in bases))
