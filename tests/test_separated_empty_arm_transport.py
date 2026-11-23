"""Frozen expected outcomes for the staged, finite transport comparison."""

import importlib
import importlib.util
import unittest
from fractions import Fraction as F
from itertools import permutations, product

from scripts import probe_colorless_packet_arms as four
from scripts import probe_eight_label_interferometer as eight


class SeparatedEmptyArmTransportTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        name = "scripts.probe_separated_empty_arm_transport"
        cls.probe = importlib.import_module(name) if importlib.util.find_spec(name) else None

    def setUp(self):
        self.assertIsNotNone(self.probe, "separated-arm transport probe is missing")

    def test_every_geometry_has_full_rows_and_exposes_the_downstream_boundary(self):
        summary = self.probe.verify()
        self.assertEqual(
            [(r.h, r.g, r.four_triggers, r.eight_triggers, r.matched_flips,
              r.four_click_changes, r.eight_click_changes) for r in summary],
            [(h, g, 512, 512, 128, 128 if g == 0 else 0, 128)
             for h, g in product(range(3), repeat=2)],
        )

    def test_four_lane_contacts_and_end_adapters_are_local_and_use_fresh_stock(self):
        probe = self.probe
        for h, g, source, seed, plates in product(
            range(3), range(3), four.ARMS, four.SOURCE_SEEDS, four.SWITCHES
        ):
            trial = probe.run_four(source, seed, (0, 2), plates, (True, False), h, g)
            for start, end, hops in (("split", "before_plates", h),
                                     ("shutters", "before_analyzer", g)):
                stage = next(stage for stage in trial.stages if stage.name == end)
                upstream = trial.arms_at(start)
                expected = tuple(four.V[1] if hops and arm in four.V else arm for arm in upstream)
                self.assertEqual(trial.arms_at(end), expected)
                if not hops:
                    self.assertEqual(stage.word, ())
                    continue
                self.assertEqual([len(layer) for layer in stage.word], [4] * hops + [2])
                source_sites = next(s.arms for s in trial.stages if s.name == start)
                for layer in stage.word[:hops]:
                    next_sites = tuple(b for _, b in layer)
                    self.assertEqual(tuple(a for a, _ in layer), sum(source_sites, ()))
                    self.assertEqual(tuple(trial.initial[b] for b in next_sites), (1,) * 4)
                    source_sites = (next_sites[:2], next_sites[2:])
                self.assertEqual(source_sites, stage.arms)
                for arm, (zero, edge) in enumerate(stage.word[-1]):
                    self.assertEqual(edge, stage.arms[arm][1])
                    self.assertEqual(trial.initial[zero], 0)
                    self.assertTrue(all(state[zero] == 0 for state in trial.trace))
            self.assertEqual(sum(trial.outcome), 1)
            self.assertEqual(trial.outcome[2], int(trial.occupied_pre_plate == 1))

    def test_zero_geometry_replays_the_exact_frozen_four_trace(self):
        for source, plates, opened, seed, mask in product(
            four.ARMS, four.SWITCHES, four.SWITCHES, four.SOURCE_SEEDS, four.MASK_SEEDS
        ):
            frozen = four.run_trial(source, seed, mask, plates, opened)
            result = self.probe.run_four(source, seed, mask, plates, opened, 0, 0)
            self.assertEqual(result.trace, frozen.trace)
            self.assertEqual(result.outcome, frozen.outcome)

    def test_exact_eight_label_edges_ignore_idle_colors_and_keep_pointwise_outcomes(self):
        for idle, h, g in product(permutations(range(4)), (1, 2), (1, 2)):
            t = self.probe.run_eight(1, 1, 0, (1, 0), (False, True), (True, False), h, g,
                                     idle_stock=idle)
            frozen = eight.trial(1, 1, 0, (1, 0), (False, True), (True, False))
            self.assertEqual(t.outcome, (frozen[1], frozen[0], frozen[2]))
            for start, end, hops in (("split", "before_plates", h),
                                     ("shutters", "before_analyzer", g)):
                stage = next(s for s in t.stages if s.name == end)
                self.assertEqual(t.arms_at(start), t.arms_at(end))
                self.assertEqual(len(stage.word), 2 * hops)
                for first, second in zip(stage.word[::2], stage.word[1::2], strict=True):
                    self.assertEqual(first, second)
                    self.assertEqual(len(first), 2)
                    self.assertTrue(all(eight.number(t.initial[b]) == 0 for _, b in first))

    def test_local_empty_setting_can_remain_in_retired_raw_stock(self):
        on = (True, True)
        probe = self.probe
        base = probe.run_four(0, (1, 2), (0, 2), (False, False), on, 1, 2)
        path = base.occupied_pre_plate
        toggled = probe.run_four(0, (1, 2), (0, 2), (path == 1, path == 0), on, 1, 2)
        self.assertEqual(base.initial, toggled.initial)
        self.assertEqual(base.arms_at("before_plates"), toggled.arms_at("before_plates"))
        self.assertNotEqual(base.arms_at("plates"), toggled.arms_at("plates"))
        self.assertEqual(base.arms_at("before_analyzer"), toggled.arms_at("before_analyzer"))
        self.assertEqual(base.outcome, toggled.outcome)
        self.assertNotEqual(base.trace[-1], toggled.trace[-1])
        self.assertEqual(probe.verify_vacancy_invariant(), 9)

    def test_active_return_bus_can_read_both_remote_local_settings(self):
        for source, settings, distances in product(range(2), four.SWITCHES, ((1, 2), (2, 1), (2, 2))):
            run = self.probe.run_return_bus(source, settings, distances)
            self.assertEqual(run.destination, source ^ settings[0] ^ settings[1])
            self.assertEqual(run.visited, (True, True))
            self.assertTrue(all(raw.count(3) == 1 for raw in run.trace))

    def test_uniform_common_schedule_keeps_detector_and_loss_accounting(self):
        probe = self.probe
        h, g, source, seed, masks = 1, 1, 0, (1, 2), (0, 2)
        for opened in four.SWITCHES:
            rows = [probe.run_four(source, seed, masks, plates, opened, h, g) for plates in four.SWITCHES]
            self.assertTrue(all(t.initial == rows[0].initial for t in rows))
            for t in rows:
                self.assertEqual(t.stages[:2] + t.stages[3:], rows[0].stages[:2] + rows[0].stages[3:])
        rows = [probe.run_four(source, s, m, (False, True), (False, True), h, g).outcome
                for s, m in product(four.SOURCE_SEEDS, four.MASK_SEEDS)]
        self.assertEqual(four.frequencies(rows), (F(1, 4), F(1, 4), F(1, 2)))


if __name__ == "__main__":
    unittest.main()
