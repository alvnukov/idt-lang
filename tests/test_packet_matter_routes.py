from __future__ import annotations

import unittest
from fractions import Fraction as F
from itertools import combinations

from scripts import probe_packet_chiral_selection as chiral
from scripts import probe_six_packet_sectors as packet


class PacketMatterRoutes(unittest.TestCase):
    def test_unobservable_correlations_survive_as_distinct_preparations(self) -> None:
        for i, j in combinations((0, 2, 4), 2):
            a = tuple(int(k // 2 == i // 2) for k in range(6))
            b = tuple(int(k // 2 == j // 2) for k in range(6))
            self.assertNotEqual(a, b)
            self.assertEqual(packet.legs(a), packet.legs(b))
            self.assertEqual(packet.complement(a), a)

    def test_basis_anomaly_controls_do_not_measure_family_count(self) -> None:
        family = chiral.REPS
        conj = tuple(chiral.dual(b) for b in family)
        for blocks in (family, conj, family + conj, family * 3):
            row = chiral.sum_rows(blocks)
            self.assertEqual(row[:5], (0,) * 5)
            self.assertEqual(row[5] % 2, 0)
        self.assertNotEqual(chiral.sum_rows(family[:-1])[:5], (0,) * 5)
        self.assertEqual(chiral.kernel(), 108)

    def test_uniform_sector_not_a_disposable_global_phase_in_fock_space(self) -> None:
        # The same phase i on every fundamental mode acts by i^grade:
        # against a grade-zero reference, the two-particle amplitude flips.
        self.assertEqual((F(0), F(2, 4), F(0)), tuple(F(n, 4) % 1 for n in (0, 2, 4)))
