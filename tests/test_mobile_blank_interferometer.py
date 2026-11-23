"""Tests for a scheduled four-label transport and clean-shutter witness."""

from itertools import product
import unittest

from scripts import probe_mobile_blank_interferometer as b
from scripts.probe_packet_free_pair_record import four_label_contact


class MobileBlankInterferometerTests(unittest.TestCase):
    def test_exact_law_delta_and_one_contact_forwarding(self):
        inputs = tuple(product(range(4), repeat=2))
        self.assertEqual([pair for pair in inputs if b.contact(pair) != four_label_contact(pair)],
                         [(1, 2), (2, 1)])
        for pair in inputs:
            after = b.contact(pair)
            self.assertEqual(b.contact(after), pair)
            self.assertEqual(after.count(3), pair.count(3))
            self.assertEqual(b.contact(pair[::-1]), after[::-1])
        for x in (1, 2, 3):
            self.assertEqual(b.contact((x, 1)), (1, x))

    def test_native_splitter_and_analyzer_share_the_frozen_palindrome(self):
        a = ((0, 1), (3, 4))
        y = ((2, 1), (5, 4))
        c = (((1, 4),),)
        q = (a, y, a)
        self.assertEqual(b.SPLITTER, c + q + c + q + c + q + c)
        self.assertEqual(b.ANALYZER, b.SPLITTER)
        for source in (0, 1):
            paths = []
            for seeds in product((1, 2), repeat=2):
                trial = b.run_trial(source, (False, False), (True, True), seeds, (1, 1), (0,) * 4)
                path, left, right = b.decode(trial.split.output)
                self.assertEqual(path ^ left ^ right, source)
                self.assertEqual(trial.analyzer.output, trial.split.initial)
                paths.append(path)
            self.assertCountEqual(paths, (0, 0, 1, 1))

    def test_plate_is_a_word_on_its_own_three_cells(self):
        word = (((2, 0),), ((0, 1),), ((2, 0),), ((0, 1),), ((2, 0),))
        for pair, flipped in (((2, 1), (2, 2)), ((2, 2), (2, 1)),
                              ((3, 1), (1, 3)), ((1, 3), (3, 1))):
            trace = b.plate(pair, True)
            self.assertEqual(trace.word, word)
            self.assertEqual(trace.initial, (*pair, 0))
            self.assertEqual(trace.output, (*flipped, 0))
            self.assertTrue(all(state[2] == 0 for state in trace.states))

    def test_relays_allocate_two_distinct_fresh_cells_per_hop(self):
        for pair, hops in product(product((1, 2, 3), repeat=2), (0, 1, 2, 5)):
            witness = b.relay(pair, hops)
            self.assertEqual(witness.initial, pair + (1, 1) * hops)
            self.assertEqual(witness.output, (1, 1) * hops + pair)
            self.assertEqual(len(witness.states), 1 + 2 * hops)
            for hop, layer in enumerate(witness.word):
                self.assertEqual(layer, ((2 * hop, 2 * hop + 2), (2 * hop + 1, 2 * hop + 3)))

    def test_shutter_physically_dumps_both_old_raw_labels(self):
        word = (((0, 2), (1, 3)), ((4, 0), (5, 1)))
        for pair, replacement in product(((2, 1), (2, 2), (3, 1), (1, 3)), (1, 2)):
            trace = b.shutter(pair, False, replacement)
            self.assertEqual(trace.word, word)
            self.assertEqual(trace.initial, (*pair, 1, 1, 2, replacement))
            self.assertEqual(trace.states[2], (1, 1, *pair, 2, replacement))
            self.assertEqual(trace.output, (2, replacement, *pair, 1, 1))
            open_trace = b.shutter(pair, True, replacement)
            self.assertEqual(open_trace.states, (trace.initial,))

    def test_embedded_asymmetric_paths_preserve_slots_and_local_references(self):
        trial = b.run_trial(0, (True, True), (False, True), (2, 1), (2, 1), (0, 5, 2, 1))
        self.assertEqual(tuple(len(arm.inbound.word) for arm in trial.arms), (0, 5))
        self.assertEqual(tuple(len(arm.outbound.word) for arm in trial.arms), (2, 1))
        embedded = trial.embed()
        self.assertEqual(len(embedded.references), 6)
        self.assertEqual(len(set(embedded.references)), 6)
        self.assertEqual(len(embedded.retired), 16)
        self.assertEqual(tuple(embedded.trace.output[i] for i in embedded.retired), (1,) * 16)
        self.assertEqual(tuple(embedded.trace.output[i] for i in embedded.dumps[0]),
                         trial.arms[0].plate.output[:2])
        self.assertTrue(all(s.count(3) == 1 for s in embedded.trace.states))

    def test_closed_plate_is_invisible_per_fixed_stock_but_dump_remembers(self):
        for source, closed, other, seeds, replacements in product(
            (0, 1), (0, 1), (False, True), b.SEEDS, b.SEEDS
        ):
            opened = (closed != 0, closed != 1)
            p = (other, False) if closed else (False, other)
            q = (other, True) if closed else (True, other)
            first = b.run_trial(source, p, opened, seeds, replacements, (1, 5, 2, 0))
            second = b.run_trial(source, q, opened, seeds, replacements, (1, 5, 2, 0))
            self.assertEqual(first.outcome, second.outcome)
            self.assertEqual(first.analyzer.output, second.analyzer.output)
            self.assertNotEqual(first.arms[closed].dump, second.arms[closed].dump)

    def test_complete_factorized_fixture_and_old_program_controls(self):
        e = b.verify()
        self.assertEqual((e.endpoint_launches, e.geometries, e.joint_launches), (512, 256, 131072))
        self.assertEqual(e.joint_outcome_counts, (32768, 32768, 65536))
        self.assertEqual(e.fixed_stock_interventions, 256)
        self.assertEqual(e.legacy_original_rows_passed, 32)
        self.assertEqual((e.legacy_rows_passed, e.legacy_rows_total), (2, 32))
