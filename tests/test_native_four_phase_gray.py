"""Independent checks of the raw schedule and unconditional eight-stock tables."""

from collections import Counter
from importlib.util import find_spec
from itertools import product
import unittest


class NativeFourPhaseGrayTests(unittest.TestCase):
    def setUp(self):
        self.assertIsNotNone(find_spec("scripts.probe_native_four_phase_gray"),
                             "the frozen raw replay is not implemented")
        from scripts import probe_native_four_phase_gray
        self.p = probe_native_four_phase_gray

    def test_three_cell_plate_orbits_and_restricted_two_cell_wall(self):
        p = self.p
        self.assertEqual(p.plate_cycles(), ((4, 4), (1,) * 8 + (4,)))
        self.assertEqual(p.two_cell_wall(), (96, 0))
        self.assertEqual(p.local((1, 1, 3), p.ENCODE), (1, 3, 1))
        self.assertEqual(p.local((1, 1, 1), p.PLATE), (2, 1, 1))

    def test_native_words_restore_raw_source_and_fold_remembers_route(self):
        p = self.p
        for bit in (1, 2):
            self.assertEqual(p.local((3, bit, 1), p.CLONE), (3, bit, bit))
        for coin, middle in ((1, (3, 1, 1)), (2, (1, 3, 2))):
            self.assertEqual(p.local((3, 1, coin), p.ROUTE), middle)
        folded = [p.local((*m, 1), p.FOLD) for m in ((3, 1), (1, 3))]
        self.assertEqual({f[:2] for f in folded}, {(3, 1)})
        self.assertEqual({f[2] for f in folded}, {1, 2})
        for m in ((3, 1), (1, 3), (1, 1)):
            for bit in (1, 2):
                self.assertEqual(p.local((*m, bit), p.COMPARE),
                                 (*(m[::-1] if bit == 1 else m), bit))

    def test_same_gray_cycle_after_decoding_both_reachable_occupancies(self):
        p = self.p
        shade_cycle = ((1, 1), (2, 1), (2, 2), (1, 2))
        for n, (a, b) in enumerate(shade_cycle):
            for m, power in product((1, 3), range(5)):
                encoded = p.local((a, b, m), p.ENCODE)
                advanced = p.local(encoded, p.PLATE * power)
                self.assertEqual(p.local(advanced, p.ENCODE), (*shade_cycle[(n + power) % 4], m))

    def test_all_masks_settings_and_stocks_including_losses(self):
        p = self.p
        for shutter, opened, (x, y) in product(p.SHUTTERS, p.MASKS, p.SETTINGS):
            k = (8, 4, 0, 4)[(x - y) % 4]
            if all(opened):
                expected = (k, 8 - k, 0)
            elif not any(opened):
                expected = (0, 0, 8)
            elif shutter == "upstream_token_only":
                expected = (k // 2, (8 - k) // 2, 4)
            else:
                expected = (2, 2, 4)
            with self.subTest(shutter=shutter, opened=opened, x=x, y=y):
                rows = [p.trial(shutter, opened, (x, y), stock) for stock in p.STOCKS]
                self.assertEqual(tuple(Counter(r.outcome for r in rows)[i] for i in range(3)), expected)
                self.assertTrue(all(sum(v == 3 for v in r.final.values()) == 1 for r in rows))

    def test_upstream_dump_quarantines_entire_raw_stock(self):
        p = self.p
        for coin in (1, 2):
            for settings in p.SETTINGS:
                row = p.trial("upstream_full", (False, True), settings, (2, 2, coin))
                self.assertEqual(tuple(row.final["dump_L_" + s] for s in "abm"),
                                 (2, 2, 3 if coin == 1 else 1))
        with self.assertRaises(ValueError):
            p.trial("upstream_full", (True, True), (4, 0), (1, 1, 1))

    def test_return_dump_remembers_the_actual_plate_dependent_bit(self):
        p = self.p
        for coin, power in product((1, 2), range(4)):
            row = p.trial("return", (False, True), (power, 0), (1, 1, coin))
            self.assertEqual(row.final["dump_L_b"], (1, 1, 2, 2)[power])
            self.assertEqual(row.final["dump_L_m"], 3 if coin == 1 else 1)
            self.assertNotIn("dump_L_a", row.final)

    def test_report_counts_supplementary_controls_separately(self):
        report = self.p.verify()
        self.assertEqual(report["main_trials"], 1536)
        self.assertEqual(report["main_contacts"], 107520)
        self.assertEqual(report["supplementary_trials"], {"independent_right": 512, "right_one_step": 128})

    def test_independent_stock_and_shift_are_supplemental_interventions(self):
        p = self.p
        for x, y in p.SETTINGS:
            totals = Counter(p.trial("upstream_full", (True, True), (x, y), left,
                                     independent_right=right).outcome
                             for left, right in product(p.STOCKS, product((1, 2), repeat=2)))
            self.assertEqual(totals, {0: 16, 1: 16})
            shifted = Counter(p.trial("upstream_full", (True, True), (x, y), left,
                                      right_prep_steps=1).outcome for left in p.STOCKS)
            self.assertEqual(shifted[0], (8, 4, 0, 4)[(x - y - 1) % 4])
