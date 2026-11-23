"""Exact preparations and delayed readout for the packet-free pair record."""

import importlib
import importlib.util
import unittest
from fractions import Fraction as F
from itertools import product


class PacketFreePairRecordTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        name = "scripts.probe_packet_free_pair_record"
        cls.probe = importlib.import_module(name) if importlib.util.find_spec(name) else None

    def setUp(self):
        self.assertIsNotNone(self.probe, "packet-free pair record probe is missing")

    def test_pairing_contrast_uses_joint_blank_law_not_single_cell_marginals(self):
        for fixture, same_rates, crossed_rates in (
            (self.probe.EIGHT_LABEL, (F(1, 2), F(0), F(1, 2)),
             (F(5, 16), F(3, 16), F(1, 2))),
            (self.probe.FOUR_LABEL, (F(0), F(1, 4), F(3, 4)),
             (F(3, 16), F(1, 16), F(3, 4))),
        ):
            with self.subTest(fixture=fixture.name):
                same = self.probe.run_pairing(fixture, crossed=False)
                crossed = self.probe.run_pairing(fixture, crossed=True)
                alphabet = fixture.labels
                raw_marginal = (F(1, 2), F(1, 4), F(1, 4)) + (F(0),) * (len(alphabet) - 3)
                self.assertEqual(same.blank_marginals, (raw_marginal, raw_marginal))
                self.assertEqual(crossed.blank_marginals, same.blank_marginals)
                self.assertEqual(same.blank_joint, {
                    pair: F(1, 4) for pair in ((0, 0), (0, 2), (2, 0), (1, 1))
                })
                self.assertEqual(crossed.blank_joint, {
                    (a, b): raw_marginal[a] * raw_marginal[b]
                    for a, b in product(range(3), repeat=2)
                })
                self.assertEqual(same.occupation_rates, same_rates)
                self.assertEqual(crossed.occupation_rates, crossed_rates)

    def test_blind_pairing_and_fixed_reader_keep_every_trial(self):
        p = self.probe
        stock = (1, 1, 0, 0)
        self.assertEqual(p.prepare(p.FOUR_LABEL, stock, crossed=False), (1, 1))
        self.assertEqual(p.prepare(p.FOUR_LABEL, stock, crossed=True), (2, 2))
        self.assertEqual(p.read(p.FOUR_LABEL, (1, 1), 3), (1, 3, 1))
        self.assertEqual(p.read(p.FOUR_LABEL, (2, 2), 3), (2, 2, 3))
        self.assertEqual(p.read(p.EIGHT_LABEL, (1, 1), 4), (4, 1, 1))
        for fixture in p.FIXTURES:
            expected_trials = list(product(product(fixture.blank_stock, repeat=4),
                                           fixture.token_stock))
            for crossed in (False, True):
                run = p.run_pairing(fixture, crossed=crossed)
                self.assertEqual([(trial.stock, trial.token) for trial in run.trials],
                                 expected_trials)
                for trial in run.trials:
                    self.assertEqual(trial.occupation,
                                     tuple(map(fixture.occupied, trial.raw_outputs)))
                    self.assertIn(trial.occupation, ((1, 0, 0), (0, 1, 0), (0, 0, 1)))

    def test_alternate_blank_laws_remove_occupation_contrast(self):
        p = self.probe
        for fixture in (p.EIGHT_LABEL_VACUUM_XOR, p.FOUR_LABEL_IDENTITY_BLANK):
            with self.subTest(fixture=fixture.name):
                same = p.run_pairing(fixture, crossed=False)
                crossed = p.run_pairing(fixture, crossed=True)
                self.assertEqual(same.occupation_rates, (F(1, 4), F(1, 4), F(1, 2)))
                self.assertEqual(crossed.occupation_rates, same.occupation_rates)
                self.assertEqual(crossed.blank_marginals, same.blank_marginals)
        same = p.run_pairing(p.EIGHT_LABEL_UNIFORM_BLANK, crossed=False)
        crossed = p.run_pairing(p.EIGHT_LABEL_UNIFORM_BLANK, crossed=True)
        self.assertEqual(same.blank_joint, dict.fromkeys(product(range(4), repeat=2), F(1, 16)))
        self.assertEqual(crossed.blank_joint, same.blank_joint)
        self.assertEqual(crossed.occupation_rates, same.occupation_rates)

    def test_raw_four_label_map_is_involutive_not_a_swap_root(self):
        p = self.probe
        changed = {
            (0, 1): (0, 2), (0, 2): (0, 1), (1, 0): (2, 0), (2, 0): (1, 0),
            (3, 1): (1, 3), (1, 3): (3, 1),
        }
        for pair in product(range(4), repeat=2):
            output = p.FOUR_LABEL.contact(pair)
            self.assertEqual(output, changed.get(pair, pair))
            self.assertEqual(p.FOUR_LABEL.contact(output), pair)
            self.assertEqual(p.FOUR_LABEL.contact(pair[::-1]), output[::-1])
            self.assertEqual(sum(map(p.FOUR_LABEL.occupied, output)), pair.count(3))
        self.assertNotEqual(p.FOUR_LABEL.contact(p.FOUR_LABEL.contact((0, 1))), (1, 0))

    def test_all_binary_blank_kernels_preserve_iid_for_every_bias(self):
        bound = self.probe.verify_binary_blank_bound()
        self.assertEqual(bound.permutations, 24)
        self.assertEqual(bound.equivariant_kernels, 4)
        self.assertEqual(bound.preserves_bias, 2)
        self.assertEqual(bound.complements_bias, 2)

    def test_all_frozen_fixture_checks(self):
        self.probe.verify()


if __name__ == "__main__":
    unittest.main()
