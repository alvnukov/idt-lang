"""Exact controls for the single-photon loss and memory probe."""

import json
import subprocess
import sys
import unittest
from fractions import Fraction
from itertools import product

from scripts import probe_single_photon_loss_memory as probe

F = Fraction


class LossAndMemoryTests(unittest.TestCase):
    def test_all_pure_arm_responses_cancel_including_losses(self) -> None:
        outcomes = tuple(
            probe.OutcomeMass(*(F(n == j) for n in range(4))) for j in range(4)
        )
        for first, second in product(outcomes, repeat=2):
            for left_share in (F(0), F(1)):
                zero = probe.OutcomeMass(F(0), F(0), F(0), F(0))
                a, b = ((first, second), (zero, zero))
                if left_share == 0:
                    a, b = b, a
                scores = probe.score_probabilities(probe.additive_model(a, b))
                self.assertEqual(scores.raw_contrast, 0)
                if scores.pooled_success is not None:
                    self.assertEqual(scores.pooled_success, F(1, 2))

    def test_deterministic_mixed_routes_preserve_all_bounds(self) -> None:
        atoms = tuple(
            probe.OutcomeMass(*(F(n == j, 2) for n in range(4))) for j in range(4)
        )
        q = {(0, 0): F(1, 5), (0, 1): F(3, 10), (1, 0): F(2, 5), (1, 1): F(1, 10)}
        for a0, a1, b0, b1 in product(atoms, repeat=4):
            p = probe.additive_model((a0, a1), (b0, b1))
            scores = probe.score_probabilities(p, q)
            self.assertEqual(scores.raw_contrast, 0)
            if scores.stratified_success is not None:
                self.assertLess(scores.stratified_success, probe.stratified_supremum(q))
            if scores.pooled_success is not None:
                self.assertLessEqual(
                    scores.pooled_success, probe.pooled_majority_bound(q)
                )

    def test_fixed_mixture_preserves_none_and_double_separately(self) -> None:
        left = (
            probe.OutcomeMass(F(1, 8), F(1, 8), F(1, 4), F(0)),
            probe.OutcomeMass(F(0), F(1, 8), F(1, 8), F(1, 4)),
        )
        right = (
            probe.OutcomeMass(F(0), F(1, 4), F(0), F(1, 4)),
            probe.OutcomeMass(F(1, 2), F(0), F(0), F(0)),
        )
        table = probe.additive_model(left, right)
        self.assertEqual(
            table[0, 0], probe.OutcomeMass(F(1, 8), F(3, 8), F(1, 4), F(1, 4))
        )
        self.assertEqual(table[1, 0].double, F(1, 2))
        self.assertEqual(probe.score_probabilities(table).raw_contrast, 0)
        self.assertEqual(probe.score_probabilities(table).pooled_success, F(1, 2))
        with self.assertRaisesRegex(ValueError, "fixed"):
            probe.additive_model((left[0], right[0] + left[1]), right)
        with self.assertRaisesRegex(ValueError, "normalize"):
            probe.score_probabilities({cell: left[0] for cell in probe.CELLS})
        with self.assertRaisesRegex(ValueError, "nonnegative"):
            probe.OutcomeMass(F(-1), F(1), F(0), F(0))

    def test_eight_herald_control_and_exact_scores(self) -> None:
        raw = {
            (0, 0): probe.RawCell(8, 0, 2, 6, 0),
            (0, 1): probe.RawCell(8, 4, 1, 3, 0),
            (1, 0): probe.RawCell(8, 4, 1, 3, 0),
            (1, 1): probe.RawCell(8, 8, 0, 0, 0),
        }
        self.assertEqual(probe.count_table(probe.sharp_loss_model(F(1, 8)), 8), raw)
        score = probe.score_counts(raw)
        self.assertEqual(score.scores.raw_contrast, 0)
        self.assertEqual(score.scores.pooled_success, F(1, 2))
        self.assertEqual(score.scores.stratified_success, F(13, 20))
        self.assertEqual(score.per_trigger_status, "inconclusive_zero_contrast")
        self.assertEqual(score.observed_pooled_success, F(1, 2))

    def test_stratified_supremum_is_strict_and_sharp(self) -> None:
        q = {(0, 0): F(1, 5), (0, 1): F(3, 10), (1, 0): F(2, 5), (1, 1): F(1, 10)}
        self.assertEqual(probe.stratified_supremum(), F(3, 4))
        self.assertEqual(probe.stratified_supremum(q), F(9, 10))
        for n in (2, 10, 1000):
            t = F(1, 2 * n)
            same = probe.sharp_loss_model(t)
            self.assertEqual(same[1, 1].left, 1)
            self.assertEqual(
                probe.score_probabilities(same).stratified_success,
                F(3, 4) - t / (1 + 2 * t),
            )
            weighted = probe.score_probabilities(same, q).stratified_success
            self.assertEqual(weighted, 1 - q[1, 1] - (q[0, 1] + q[1, 0]) / (n + 1))
            self.assertLess(weighted or F(0), probe.stratified_supremum(q))
        other_corner = probe.sharp_loss_model(F(1, 2000), (0, 1))
        self.assertEqual(other_corner[0, 1].right, 1)
        self.assertGreater(
            probe.score_probabilities(other_corner).stratified_success or F(0),
            F(749, 1000),
        )
        with self.assertRaisesRegex(ValueError, "positive"):
            probe.stratified_supremum(dict.fromkeys(probe.CELLS, F(0)))

    def test_biased_pooled_cap_and_nonoptimal_responses(self) -> None:
        q = {(0, 0): F(1, 5), (0, 1): F(3, 10), (1, 0): F(2, 5), (1, 1): F(1, 10)}
        self.assertEqual(probe.pooled_majority_bound(q), F(4, 5))
        # Left arm only: accept x=1 and return its majority guess y=0.
        no = probe.OutcomeMass(F(0), F(0), F(1), F(0))
        reject = probe.OutcomeMass(F(0), F(0), F(0), F(0))
        good = probe.OutcomeMass(F(1), F(0), F(0), F(0))
        bad = probe.OutcomeMass(F(0), F(1), F(0), F(0))
        for outcome, expected in ((good, F(4, 5)), (bad, F(1, 5))):
            p = probe.additive_model((no, outcome), (reject, reject))
            self.assertEqual(probe.score_probabilities(p, q).pooled_success, expected)

    def test_only_known_positive_trigger_denominators_can_score_raw(self) -> None:
        complete = probe.count_table(probe.sharp_loss_model(F(0)), 2)
        no_click = probe.score_counts(complete)
        self.assertEqual(no_click.scores.raw_contrast, 0)
        self.assertEqual(no_click.scores.pooled_success, F(1, 2))
        self.assertIsNone(no_click.scores.stratified_success)
        for row in (
            {(0, 0): probe.RawCell(0, 0, 0, 0, 0)},
            {(0, 0): probe.RawCell(None, 0, 0, None, None)},
            {(0, 0): probe.RawCell(2, 0, 0, None, None)},
            {},
        ):
            altered = {
                cell: value for cell, value in complete.items() if cell != (0, 0)
            }
            altered.update(row)
            raw = probe.score_counts(altered)
            self.assertIsNone(raw.scores.raw_contrast)
            self.assertEqual(
                raw.per_trigger_status, "inconclusive_missing_denominators"
            )
        all_dark = dict.fromkeys(probe.CELLS, probe.RawCell(2, 0, 0, 1, 1))
        self.assertEqual(probe.score_counts(all_dark).scores.raw_contrast, 0)
        self.assertIsNone(probe.score_counts(all_dark).scores.pooled_success)
        with self.assertRaisesRegex(ValueError, "account"):
            probe.RawCell(4, 1, 1, 1, 0)

    def test_equal_cell_standardization_is_not_observed_biased_pooling(self) -> None:
        raw = probe.count_table(probe.sharp_loss_model(F(1, 8)), 8)
        raw[0, 0] = probe.RawCell(16, 0, 4, 12, 0)
        score = probe.score_counts(raw)
        self.assertEqual(score.scores.raw_contrast, F(0))
        self.assertEqual(score.scores.pooled_success, F(1, 2))
        self.assertEqual(score.observed_pooled_success, F(6, 11))

    def test_cross_setting_rejection_not_local_and_postselected_is_inconclusive(
        self,
    ) -> None:
        full, reported = probe.cross_setting_rejection()
        full_scores = probe.score_counts(full)
        self.assertEqual(full_scores.scores.raw_contrast, F(1, 2))
        self.assertEqual(full_scores.scores.pooled_success, 1)
        self.assertEqual(full_scores.scores.stratified_success, 1)
        self.assertTrue(all(row.none == 1 and row.double == 1 for row in full.values()))
        self.assertIsNone(probe.score_counts(reported).scores.raw_contrast)
        self.assertEqual(
            probe.score_counts(reported).per_trigger_status,
            "inconclusive_missing_denominators",
        )

    def test_lossless_joint_reference_has_both_contrast_orientations(self) -> None:
        for inverted, expected in ((False, 1), (True, -1)):
            table = probe.joint_reference(inverted=inverted)
            scores = probe.score_counts(table).scores
            self.assertEqual(scores.raw_contrast, expected)
            self.assertEqual(scores.pooled_success, (1 + expected) // 2)

    def test_repeated_schedule_and_fresh_schedule_replay_raw_shots(self) -> None:
        for n in (1, 2, 3):
            repeated = probe.replay_memory(n, fresh_settings=False)
            fresh = probe.replay_memory(n, fresh_settings=True)
            per_shot = tuple(
                probe.score_counts(row).scores.pooled_success for row in repeated
            )
            self.assertEqual(
                per_shot, tuple(probe.memory_shot_success(k) for k in range(1, n + 1))
            )
            expected = tuple(probe.memory_shot_success(k) for k in range(1, n + 1))
            self.assertEqual(sum(expected) / n, probe.memory_block_success(n))
            for counts in fresh:
                self.assertTrue(all(row.left == row.right for row in counts.values()))
                self.assertEqual(probe.score_counts(counts).scores.raw_contrast, 0)
            self.assertEqual(
                sum(row.triggers or 0 for row in repeated[-1].values()), 4 * 4**n
            )
            self.assertEqual(
                sum(row.triggers or 0 for row in fresh[-1].values()), 16**n
            )
        with self.assertRaises(ValueError):
            probe.memory_shot_success(0)
        with self.assertRaises(ValueError):
            probe.replay_memory(5, fresh_settings=True)

    def test_cli_report_is_deterministic_and_large_n_is_compact(self) -> None:
        cmd = [sys.executable, "-B", "scripts/probe_single_photon_loss_memory.py"]
        first = subprocess.check_output(cmd)
        self.assertEqual(first, subprocess.check_output(cmd))
        self.assertLess(len(first), 14000)
        data = json.loads(first)
        self.assertEqual(
            data["uniform_eight_herald_control"]["scores"]["stratified_success"],
            "13/20",
        )
        self.assertEqual(
            data["memory"]["repeated_settings_large_block"]["shots"], 15000
        )
        self.assertEqual(
            data["memory"]["repeated_settings_large_block"]["mean_formula"],
            "1 - (1 - 2**(-15000))/15000",
        )
        self.assertIs(
            data["published_context"]["per_trigger_table_available_in_article"], False
        )


if __name__ == "__main__":
    unittest.main()
