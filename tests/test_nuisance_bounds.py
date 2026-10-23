"""Exact conditional controls; supplied toy bounds are not actual calibration."""

from __future__ import annotations

import hashlib
import subprocess
import sys
import unittest
from dataclasses import replace
from fractions import Fraction
from pathlib import Path
from typing import Any
from unittest.mock import patch

from theory_experiments import raw_signal_replay as raw
from theory_experiments.nuisance_bounds import (
    NuisanceBounds,
    ReplayTarget,
    ScalarInterval,
    SuppliedBound,
    assess_epsilon,
    transfer,
)

TARGET = ReplayTarget("toy", "a" * 64, "b" * 64)


def interval(lower: int, upper: int) -> ScalarInterval:
    return ScalarInterval(Fraction(lower), Fraction(upper))


def bound(kind: str, lower: int, upper: int, target: ReplayTarget = TARGET) -> SuppliedBound:
    return SuppliedBound(interval(lower, upper),
                         "sampling_measurement_error" if kind == "sampling" else "apparatus_context_switch_bias",
                         "recorded_minus_expected" if kind == "sampling" else "expected_minus_ideal",
                         target, "hypothetical-control-not-apparatus-calibration",
                         ("asserted simultaneous toy bounds only",),
                         "supplied_deterministic_bound", False, "mean_cycle_epsilon", "volt")


class NuisanceBoundTests(unittest.TestCase):
    def test_nonzero_recording_without_error_excludes_only_joint_null(self) -> None:
        result = assess_epsilon(Fraction(1), TARGET, NuisanceBounds(bound("sampling", 0, 0), bound("bias", 0, 0)))
        self.assertEqual(result.q_interval, interval(1, 1))
        self.assertEqual(result.status, "conditional_joint_null_bridge_bounds_inconsistent")
        self.assertEqual(result.as_report()["candidate_verdict"], "not_assessed")

    def test_bias_can_explain_nonzero_or_mask_a_signal(self) -> None:
        explained = assess_epsilon(Fraction(1), TARGET, NuisanceBounds(bound("sampling", 0, 0), bound("bias", 1, 1)))
        self.assertEqual(explained.q_interval, interval(0, 0))
        self.assertEqual(explained.status, "zero_not_excluded_by_supplied_bounds")
        masked = assess_epsilon(Fraction(0), TARGET, NuisanceBounds(bound("sampling", 0, 0), bound("bias", -1, -1)))
        self.assertEqual(masked.q_interval, interval(1, 1))
        self.assertEqual(masked.status, "conditional_joint_null_bridge_bounds_inconsistent")

    def test_zero_endpoints_are_not_excluded(self) -> None:
        for ehat in (Fraction(1), Fraction(-1)):
            result = assess_epsilon(ehat, TARGET, NuisanceBounds(bound("sampling", -1, 1), bound("bias", 0, 0)))
            self.assertEqual(result.status, "zero_not_excluded_by_supplied_bounds")

    def test_missing_either_or_both_never_defaults_to_zero(self) -> None:
        for supplied, missing in ((NuisanceBounds(), ("sampling", "bias")),
                                  (NuisanceBounds(bound("sampling", 0, 0)), ("bias",)),
                                  (NuisanceBounds(bias=bound("bias", 0, 0)), ("sampling",))):
            with self.subTest(missing=missing):
                result = assess_epsilon(Fraction(100), TARGET, supplied)
                self.assertEqual(result.status, "inconclusive_missing_bounds")
                self.assertEqual(result.missing_bounds, missing)
                self.assertIsNone(result.q_interval)

    def test_exact_signed_rational_transfer_and_endpoint_witnesses(self) -> None:
        ehat = Fraction(-2, 7)
        sampling = ScalarInterval(Fraction(-1, 3), Fraction(2, 5))
        bias = ScalarInterval(Fraction(-4, 9), Fraction(-1, 11))
        enclosure = transfer(ehat, sampling, bias)
        self.assertEqual(enclosure.lower, Fraction(-229, 385))
        self.assertEqual(enclosure.upper, Fraction(31, 63))
        for s, b, q in ((sampling.upper, bias.upper, enclosure.lower),
                        (sampling.lower, bias.lower, enclosure.upper)):
            mu = ehat - s
            self.assertEqual(mu - q, b)
            self.assertTrue(sampling.lower <= ehat - mu <= sampling.upper)
            self.assertTrue(bias.lower <= mu - q <= bias.upper)

    def test_widening_either_bound_cannot_newly_exclude_zero(self) -> None:
        ehat = Fraction(1)
        narrow_s, narrow_b = interval(0, 1), interval(0, 0)
        original = transfer(ehat, narrow_s, narrow_b)
        self.assertTrue(original.contains_zero)
        for sampling, bias in ((interval(-2, 3), narrow_b), (narrow_s, interval(-3, 7)),
                               (interval(-2, 3), interval(-3, 7))):
            widened = transfer(ehat, sampling, bias)
            self.assertLessEqual(widened.lower, original.lower)
            self.assertGreaterEqual(widened.upper, original.upper)
            self.assertTrue(widened.contains_zero)

    def test_bad_numeric_shapes_are_contract_errors(self) -> None:
        malformed: list[Any] = [0, True, .1, float("nan"), float("inf"), "1/2", None]
        for value in malformed:
            with self.subTest(value=value), self.assertRaises(ValueError):
                ScalarInterval(value, Fraction(1))
            with self.subTest(ehat=value), self.assertRaises(ValueError):
                assess_epsilon(value, TARGET)
        with self.assertRaises(ValueError):
            ScalarInterval(Fraction(2), Fraction(1))

    def test_wrong_quantity_sign_observable_unit_and_binding_are_errors(self) -> None:
        sampling, bias = bound("sampling", 0, 0), bound("bias", 0, 0)
        wrong: list[dict[str, Any]] = [
            {"quantity": "apparatus_context_switch_bias"}, {"sign_convention": "expected_minus_recorded"},
            {"observable": "Peres_DeltaF"}, {"unit": "rad"},
            {"target": replace(TARGET, run_id="another")},
            {"target": replace(TARGET, raw_sha256="c" * 64)},
            {"target": replace(TARGET, recipe_sha256="d" * 64)}]
        for change in wrong:
            with self.subTest(change=change), self.assertRaisesRegex(ValueError, "contract mismatch"):
                assess_epsilon(Fraction(1), TARGET, NuisanceBounds(replace(sampling, **change), bias))
        with self.assertRaisesRegex(ValueError, "contract mismatch"):
            assess_epsilon(Fraction(1), TARGET, NuisanceBounds(bias, sampling))

    def test_bad_provenance_is_not_eligible_by_default(self) -> None:
        for changes in ({"source_ref": " "}, {"assumptions": ()}, {"assumptions": ("",)},
                        {"depends_on_tested_null": "false"}, {"evidence_kind": ""}):
            with self.subTest(changes=changes), self.assertRaises(ValueError):
                replace(bound("sampling", 0, 0), **changes)
        for digest in ("a" * 63, "A" * 64, "z" * 64):
            with self.assertRaises(ValueError):
                ReplayTarget("toy", digest, "b" * 64)

    def test_eligibility_observable_and_unit_metadata_cannot_be_omitted(self) -> None:
        full: dict[str, Any] = dict(vars(bound("sampling", 0, 0)))
        for name in ("evidence_kind", "depends_on_tested_null", "observable", "unit"):
            omitted = {key: value for key, value in full.items() if key != name}
            with self.subTest(omitted=name), self.assertRaises(TypeError):
                SuppliedBound(**omitted)

    def test_sd_sem_ci_and_unknown_evidence_never_become_bounds(self) -> None:
        for evidence in ("SD", "SEM", "confidence_interval", "unknown"):
            for slot in ("sampling", "bias"):
                sampling, bias = bound("sampling", 0, 0), bound("bias", 0, 0)
                if slot == "sampling":
                    sampling = replace(sampling, evidence_kind=evidence)
                else:
                    bias = replace(bias, evidence_kind=evidence)
                result = assess_epsilon(Fraction(1), TARGET, NuisanceBounds(sampling, bias))
                self.assertEqual(result.status, "unsupported_evidence_kind")
                self.assertIsNone(result.q_interval)

    def test_explicit_null_dependence_unsupported_even_if_labeled_bound(self) -> None:
        bias = replace(bound("bias", 1, 1), depends_on_tested_null=True)
        result = assess_epsilon(Fraction(1), TARGET, NuisanceBounds(bound("sampling", 0, 0), bias))
        self.assertEqual(result.status, "unsupported_circular_null_calibration")
        self.assertIsNone(result.q_interval)

    def test_unknown_kind_containing_circular_label_does_not_declare_null_dependence(self) -> None:
        bias = replace(bound("bias", 0, 0), evidence_kind="unsupported_circular_null_calibration")
        result = assess_epsilon(Fraction(1), TARGET, NuisanceBounds(bound("sampling", 0, 0), bias))
        self.assertEqual(result.status, "unsupported_evidence_kind")
        self.assertFalse(bias.depends_on_tested_null)
        self.assertIsNone(result.q_interval)

    def test_ineligible_supplied_evidence_dominates_missing_slot_without_hiding_it(self) -> None:
        for evidence, null_dependent, expected in (
                ("SEM", False, "unsupported_evidence_kind"),
                ("supplied_deterministic_bound", True, "unsupported_circular_null_calibration")):
            sampling = replace(bound("sampling", 0, 0), evidence_kind=evidence,
                               depends_on_tested_null=null_dependent)
            result = assess_epsilon(Fraction(1), TARGET, NuisanceBounds(sampling=sampling))
            self.assertEqual(result.status, expected)
            self.assertEqual(result.missing_bounds, ("bias",))
            self.assertIsNone(result.q_interval)
            with self.assertRaisesRegex(ValueError, "contract mismatch"):
                assess_epsilon(Fraction(1), TARGET, NuisanceBounds(
                    sampling=sampling, bias=replace(bound("bias", 0, 0), unit="rad")))

    def test_same_data_without_null_dependence_remains_conditional_not_certified(self) -> None:
        sampling = replace(bound("sampling", 0, 1), source_ref=f"same-data-sha256:{TARGET.raw_sha256}")
        bias = replace(bound("bias", 0, 1), source_ref=sampling.source_ref)
        report = assess_epsilon(Fraction(1), TARGET, NuisanceBounds(sampling, bias)).as_report()
        self.assertEqual(report["status"], "zero_not_excluded_by_supplied_bounds")
        self.assertIn("not_bound_certification", str(report["scope"]))

    def test_zero_epsilon_does_not_imply_quadratic_model_feasibility(self) -> None:
        # Under supplied nonnegative quadratic/common zero-background assumptions,
        # weights pA=pB=1 require pAB <= (sqrt(1)+sqrt(1))^2=4, but pAB=9.
        result = raw.reduce_cycle([(i, (float(p),)) for i, p in enumerate([0, 1, 1, 9, 1, 1, 1, 8])])
        self.assertEqual(result.epsilon, 0)
        self.assertGreater(result.means[3], 4)
        assessment = assess_epsilon(result.epsilon, TARGET, NuisanceBounds(bound("sampling", 0, 0), bound("bias", 0, 0)))
        self.assertEqual(assessment.status, "zero_not_excluded_by_supplied_bounds")
        self.assertEqual(assessment.as_report()["zero_retained_meaning"], "not_acceptance_or_model_feasibility")

    def test_fixed_open_closed_amplitudes_cancel_but_cross_influence_and_nonlinearity_need_not(self) -> None:
        closed = ((1, 2), (-2, 1), (3, -1))
        opened = ((2, 3), (1, -2), (-1, 4))
        values = []
        for mask in range(8):
            paths = [opened[i] if mask & (1 << i) else closed[i] for i in range(3)]
            x, y = sum(a[0] for a in paths), sum(a[1] for a in paths)
            values.append(float(3 * (x * x + 2 * y * y) + 7))
        reduction = raw.reduce_cycle([(i, (p,)) for i, p in enumerate(values)])
        self.assertEqual(reduction.epsilon, 0)
        self.assertNotEqual(values[0], 7)  # empty includes coherent closed paths
        changed = values.copy()
        changed[7] += 1
        self.assertEqual(raw.reduce_cycle([(i, (p,)) for i, p in enumerate(changed)]).epsilon, 1)
        self.assertNotEqual(raw.reduce_cycle([(i, (p * p,)) for i, p in enumerate(values)]).epsilon, 0)


class ReplayBoundsIntegrationTests(unittest.TestCase):
    def test_cached_dependency_stale_before_raw_import_is_rejected(self) -> None:
        # The altered loaded identity simulates an edit AFTER dependency import
        # but BEFORE raw replay import; raw's own disk snapshot cannot detect it.
        code = ("import theory_experiments.nuisance_bounds as n; "
                "n.LOADED_SOURCE_SHA256 = '0' * 64; "
                "import theory_experiments.raw_signal_replay")
        result = subprocess.run([sys.executable, "-c", code], cwd=raw.ROOT,
                                capture_output=True, text=True, check=False)
        self.assertNotEqual(result.returncode, 0)
        self.assertIn("nuisance bounds source changed since import", result.stderr)

    def test_operator_supplied_bounds_bind_actual_computed_estimator(self) -> None:
        source = raw.registry()["runs"][0]
        recipe_sha = hashlib.sha256(raw.canonical_json(raw.RECIPE).encode()).hexdigest()
        target = ReplayTarget(source["id"], source["sha256"], recipe_sha)
        supplied = NuisanceBounds(bound("sampling", 0, 0, target), bound("bias", 1, 1, target))
        fake_run = {"primary_all_cycles": {"mean_epsilon_volt": raw.number(Fraction(1))}}
        with patch.object(raw, "_read_run", side_effect=lambda *_: {**fake_run}):
            report = raw.replay(Path("/unused"), bounds_by_run={source["id"]: supplied})
        runs: Any = report["runs"]
        self.assertEqual(runs[0]["nuisance_assessment"]["status"], "zero_not_excluded_by_supplied_bounds")
        self.assertEqual(runs[1]["nuisance_assessment"]["status"], "inconclusive_missing_bounds")
        self.assertEqual(report["candidate_verdict"], "not_assessed")
        self.assertEqual(report["schema"], "idt-gstir2021-raw-replay/2")

    def test_unknown_run_rejected_before_reading(self) -> None:
        with patch.object(raw, "_read_run") as read, self.assertRaisesRegex(ValueError, "unknown fixed run"):
            raw.replay(Path("/unused"), bounds_by_run={"unknown": NuisanceBounds()})
        read.assert_not_called()

    def test_provenance_covers_new_operative_paths_and_actual_bounds_remain_missing(self) -> None:
        hashes = raw.provenance()
        for path in ("theory_experiments/nuisance_bounds.py", "Proofs/QMClosure/SorkinErrorBudget.lean",
                     "Proofs/MetaLang/V8CheckerResearchProgram.lean", "lakefile.lean"):
            self.assertIn(path, hashes)
        audit = raw.registry()["nuisance_evidence"]
        self.assertIsNone(audit["actual_supported_sampling_bound"])
        self.assertIsNone(audit["actual_supported_bias_bound"])
        self.assertTrue(all(item["source_url"].startswith("https://") for item in audit["items"]))


if __name__ == "__main__":
    unittest.main()
