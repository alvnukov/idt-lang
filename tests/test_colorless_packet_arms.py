"""Exact finite readout and shutter controls for the colorless-packet arms."""

import importlib
import importlib.util
import unittest
from collections import Counter
from fractions import Fraction as F
from itertools import product

from scripts.probe_packet_free_pair_record import four_label_contact


class ColorlessPacketArmsTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        name = "scripts.probe_colorless_packet_arms"
        cls.p = importlib.import_module(name) if importlib.util.find_spec(name) else None

    def setUp(self):
        self.assertIsNotNone(self.p, "colorless packet arms probe is missing")

    def test_frozen_contact_is_a_number_preserving_involution_not_a_swap_root(self):
        p = self.p
        self.assertIs(p.four_label_contact, four_label_contact)
        changed = {
            (0, 1): (0, 2), (0, 2): (0, 1), (1, 0): (2, 0), (2, 0): (1, 0),
            (3, 1): (1, 3), (1, 3): (3, 1),
        }
        for pair in product(range(4), repeat=2):
            image = p.four_label_contact(pair)
            self.assertEqual(image, changed.get(pair, pair))
            self.assertEqual(p.four_label_contact(image), pair)
            self.assertEqual(p.four_label_contact(pair[::-1]), image[::-1])
            self.assertEqual(image.count(3), pair.count(3))
        self.assertEqual(p.verify_raw_contact(), 16)
        self.assertNotEqual(p.four_label_contact(p.four_label_contact((0, 1))), (1, 0))

    def test_splitter_preserves_input_parity_and_analyzer_recovers_full_raw_stock(self):
        p = self.p
        encoded_states = set()
        for source in (0, 1):
            paths = Counter()
            for seeds in product((1, 2), repeat=2):
                trial = p.run_trial(source, seeds, (0, 2), (False, False), (True, True))
                path, left, right = p.decode(trial.split)
                encoded_states.add(trial.split)
                paths[path] += 1
                self.assertEqual(path ^ left ^ right, source)
                self.assertEqual(trial.output, trial.initial)
                mirrored = p.run_trial(1 - source, seeds[::-1], (2, 0),
                                       (False, False), (True, True))
                self.assertEqual(p.decode(mirrored.split), (1 - path, right, left))
            self.assertEqual(paths, {0: 2, 1: 2})
        self.assertEqual(len(encoded_states), 8)
        self.assertEqual(p.verify_code(), 8)

    def test_plates_toggle_only_the_selected_arm_code_bit_and_restore_references(self):
        p = self.p
        for source, seeds, plates in product((0, 1), product((1, 2), repeat=2), p.SWITCHES):
            trial = p.run_trial(source, seeds, (0, 2), plates, (True, True))
            path, left, right = p.decode(trial.split)
            self.assertEqual(p.decode(trial.plated), (path, left ^ plates[0], right ^ plates[1]))
            self.assertEqual(tuple(trial.plated[i] for i in p.ZERO), (0, 0))
            self.assertEqual(tuple(trial.output[i] for i in p.DETECTOR).index(3),
                             source ^ plates[0] ^ plates[1])

    def test_all_rows_keep_every_launch_and_account_for_permanent_dump_loss(self):
        p = self.p
        rows = p.enumerate_rows()
        self.assertEqual(len(rows), 32)
        self.assertEqual(sum(map(len, rows.values())), 512)
        for (source, plates, opened), trials in rows.items():
            with self.subTest(source=source, plates=plates, opened=opened):
                self.assertEqual([(trial.source_seed, trial.mask_seed) for trial in trials],
                                 list(product(product((1, 2), repeat=2), product((0, 2), repeat=2))))
                destination = source ^ plates[0] ^ plates[1]
                if all(opened):
                    expected = (F(1 - destination), F(destination), F(0))
                elif any(opened):
                    expected = (F(1, 4), F(1, 4), F(1, 2))
                else:
                    expected = (F(0), F(0), F(1))
                self.assertEqual(p.rates(trials), expected)
                baseline = p.eight_label_rates(source, plates, opened)
                self.assertEqual(expected, (baseline[1], baseline[0], baseline[2]))
                for trial in trials:
                    path, _, _ = p.decode(trial.split)
                    self.assertTrue(all(state.count(3) == 1 for state in trial.trace))
                    self.assertEqual(trial.outcome[2], int(not opened[path]))
                    self.assertEqual(sum(trial.outcome), 1)
                    self.assertEqual(tuple(trial.output[i] for i in p.DUMP),
                                     tuple(trial.shuttered[i] for i in p.DUMP))

    def test_fixed_new_stock_exposes_closed_arm_plate_memory(self):
        p = self.p
        for source, closed, other_plate in product((0, 1), repeat=3):
            for fixed_mask in (0, 2):
                zero = p.fixed_mask_rates(source, closed, False, bool(other_plate), fixed_mask)
                one = p.fixed_mask_rates(source, closed, True, bool(other_plate), fixed_mask)
                other_mask = p.fixed_mask_rates(source, closed, False, bool(other_plate), 2 - fixed_mask)
                self.assertIn(zero, ((F(1, 2), F(0), F(1, 2)), (F(0), F(1, 2), F(1, 2))))
                self.assertEqual(one, (zero[1], zero[0], zero[2]))
                self.assertEqual(other_mask, one)
                opened = tuple(i != closed for i in (0, 1))
                no_closed_plate = tuple(bool(other_plate) if i != closed else False for i in (0, 1))
                closed_plate = tuple(bool(other_plate) if i != closed else True for i in (0, 1))
                stock_phase = fixed_mask // 2
                baseline = p.eight_label_rates(source, no_closed_plate, opened, fixed_closed=stock_phase)
                self.assertEqual(baseline, p.eight_label_rates(source, closed_plate, opened,
                                                               fixed_closed=stock_phase))
                self.assertEqual(baseline[2], F(1, 2))

    def test_shutter_keeps_or_flips_vacant_code_and_sends_only_the_token_to_dump(self):
        p = self.p
        for pair, before_mask, dumped in ((p.O[0], 1, 3), (p.O[1], 0, 3),
                                          (p.V[0], 0, 1), (p.V[1], 1, 1)):
            for mask, flips in ((0, 1), (2, 0)):
                initial = (*pair, 0, 1, 1, 0, 1, mask, 1, 2)
                raw = p.replay(initial, p.shutter_word((False, True)))[-1]
                self.assertEqual(raw, (*p.V[before_mask ^ flips], 0, 1, 1, 0, dumped, mask, 1, 2))

    def test_schedule_is_mirror_symmetric_and_label_conjugation_changes_no_readout(self):
        p = self.p
        self.assertEqual(p.max_degree(p.schedule((True, True), (True, True))), 3)
        self.assertEqual(p.max_degree(p.schedule((True, True), (False, False))), 4)
        for (source, plates, opened), trials in p.enumerate_rows().items():
            for trial in trials:
                mirror = p.run_trial(1 - source, trial.source_seed[::-1], trial.mask_seed[::-1],
                                     plates[::-1], opened[::-1])
                self.assertEqual(mirror.outcome, (trial.outcome[1], trial.outcome[0], trial.outcome[2]))
                self.assertEqual(mirror.output, p.mirror(trial.output))
                self.assertEqual(p.relabel_replay(trial, plates, opened),
                                 tuple(p.relabel(state) for state in trial.trace))

    def test_probe_verifies_without_unittest(self):
        self.assertEqual(self.p.verify(), (512, 32, 16))


if __name__ == "__main__":
    unittest.main()
