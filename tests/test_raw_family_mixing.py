from __future__ import annotations

import unittest
from fractions import Fraction as F

from scripts import probe_ckm_blank_ports as blanks
from scripts import probe_ckm_raw_family_wall as wall
from scripts.gaussian_dyadic_words import ONE, ZERO, apply, eye, g, unitary


class RawFamilyMixingTests(unittest.TestCase):
    def test_pinned_numbers_have_distinct_provenance(self) -> None:
        self.assertEqual(wall.PDG[0][1].central, F(22501, 100000))
        self.assertEqual(wall.PDG[2][1].high, F(4188, 100000))
        self.assertEqual(blanks.target_gap(), F(180028, 3000000))
        self.assertEqual(
            wall.three_input_control()["a_times_one_minus_b_minus_b_minus_c_lower"],
            "59/500",
        )

    def test_leakage_bound_is_one_sided_and_weakens_with_uncertainty(self) -> None:
        gap = blanks.target_gap()
        central = blanks.minimum_one_spare_leakage(F(0), gap)
        self.assertEqual(blanks.minimum_one_spare_leakage(gap / 2, gap), central / 4)
        self.assertEqual(blanks.minimum_one_spare_leakage(gap + F(1, 100), gap), 0)
        with self.assertRaises(ValueError):
            blanks.minimum_one_spare_leakage(F(-1, 10), gap)

    def test_six_raw_mixers_saturate_reference_geometry(self) -> None:
        u = eye(4)
        for j, k in ((0, 1), (2, 3), (0, 2), (1, 3), (0, 3), (1, 2)):
            u = apply(u, ("T", j, k))
        self.assertEqual(
            u,
            tuple(tuple(g(F(1, 2) - int(i == j)) for j in range(4)) for i in range(4)),
        )
        d = u[3][3]
        leak = 1 - d.norm2()
        self.assertEqual((ONE - d).norm2(), 3 * leak)
        self.assertEqual(F(8, 3) * (1 - d.re), F(16, 3) * leak)

    def test_two_spare_reference_changes_data_determinant_without_loss(self) -> None:
        raw = blanks.two_spare_reference()
        block = tuple(r[:3] for r in raw[:3])
        self.assertTrue(unitary(block))
        self.assertTrue(all(z == ZERO for r in raw[3:] for z in r[:3]))
        self.assertEqual(wall.determinant(block), g(F(15, 17), F(8, 17)))
        self.assertFalse(
            wall.triangle_squared(tuple(block[i][j].norm2() for i, j in wall.CYCLES[0]))
        )
        self.assertEqual(sum(block[0], ZERO), ONE)

    def test_subblock_range_diagnostic_does_not_treat_ignorance_as_success(
        self,
    ) -> None:
        pdg = tuple(tuple((e.low, e.high) for e in r) for r in wall.PDG)
        result = blanks.one_spare_box(pdg)
        self.assertEqual(result.status, "excluded_one_raw_spare")
        self.assertEqual(
            result.cyclic_leakage_lower - result.leakage_upper, F(".000075844428")
        )
        loose = tuple(tuple((F(0), hi) for _, hi in r) for r in pdg)
        self.assertEqual(blanks.one_spare_box(loose).status, "inconclusive")
        impossible = tuple(((F(1), F(1)),) * 3 for _ in range(3))
        self.assertEqual(
            blanks.one_spare_box(impossible).status,
            "incompatible_with_a_unitary_subblock",
        )
        with self.assertRaises(ValueError):
            blanks.one_spare_box(())
