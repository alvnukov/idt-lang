from __future__ import annotations

import unittest
from fractions import Fraction as F

from scripts import compare_exchange_phases as compare
from scripts import probe_packet_exchange_cycles as ring
from scripts.gaussian_dyadic_words import ONE, ZERO, I, g


class SourceExchangeControls(unittest.TestCase):
    def test_mismatch_contains_observable_cycle_not_an_arbitrary_ray_phase(
        self,
    ) -> None:
        a, b = ring.sources(4, 0), ring.sources(4, 2)
        result = compare.compare(a, b)
        self.assertEqual(result.kind, "cycle-phase")
        self.assertEqual(len(set(result.witness)), 4)
        self.assertEqual(compare.loop_value(a, result.witness), g(F(1, 16)))
        self.assertEqual(compare.loop_value(b, result.witness), g(F(-1, 16)))
        self.assertEqual(ring.experiment(4, 2, 0), (F(1, 8), F(-1, 16)))

    def test_zero_overlap_singular_matrices_and_global_phase(self) -> None:
        a = ((ONE, ONE, ZERO), (ONE, ONE, ZERO), (ZERO, ZERO, ONE))
        b = ((ONE, I, ZERO), (I.star(), ONE, ZERO), (ZERO, ZERO, ONE))
        r = compare.compare(a, b)
        self.assertEqual(r.kind, "rephasing-equivalent")
        self.assertEqual(r.phases, (ONE, I, ONE))
        self.assertEqual(
            compare.compare(
                a, ((ONE, ZERO, ZERO), (ZERO, ONE, ZERO), (ZERO, ZERO, ONE))
            ).kind,
            "pair-magnitude",
        )

    def test_invalid_psd_is_not_treated_as_an_exclusion(self) -> None:
        with self.assertRaises(ValueError):
            compare.compare(((ONE, g(2)), (g(2), ONE)), ((ONE, ZERO), (ZERO, ONE)))
        with self.assertRaises(ValueError):
            compare.validated(((ONE, ONE, ZERO), (ONE, ONE, ONE), (ZERO, ONE, ONE)))
        with self.assertRaises(TypeError):
            compare.parse_scalar(0.5)
