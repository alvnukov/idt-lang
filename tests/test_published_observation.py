"""Published-summary arithmetic and explicit bridge walls, not empirical acceptance."""

from __future__ import annotations

import copy
import io
import json
import tempfile
import unittest
from contextlib import redirect_stderr, redirect_stdout
from fractions import Fraction
from pathlib import Path
from unittest.mock import patch

from scripts.archive_existing_primitives import inventory_specifications
from scripts.screen_hypotheses import main as screen_main
from theory_experiments import candidate_pipeline as pipeline
from theory_experiments import published_observation as observation
from theory_experiments.amplitude_algebra import (
    AmplitudeAlgebra,
    parse_amplitude_algebra,
)
from theory_experiments.candidate_history import (
    History,
    recheck_history,
    record_batch,
    semantic_report,
)
from theory_experiments.primitive_screen import (
    Limits,
    canonical_json,
    load_json,
    object_fields,
    parse_limits,
)

CONTROLS = pipeline.ROOT / "data/published_observation_controls.json"


def fixtures() -> dict[str, dict[str, object]]:
    values = load_json(CONTROLS)
    assert isinstance(values, list)
    return {str(object_fields(value)["id"]): object_fields(value) for value in values}


def run(name: str = "observation_gaussian") -> dict[str, object]:
    return pipeline.run_batch([fixtures()[name]], fresh=True)[0].report


class PublishedObservationTests(unittest.TestCase):
    def test_exact_independent_descriptive_arithmetic_no_model_ranking(self) -> None:
        reports = [run(f"observation_{name}") for name in ("scalar", "gaussian", "dual")]
        comparisons = []
        for report in reports:
            scope = object_fields(report["scope"])
            prediction = object_fields(scope["prediction"])
            comparison = object_fields(scope["comparison"])
            self.assertEqual(prediction["ideal_epsilon"], "0")
            self.assertEqual(prediction["ideal_kappa"], "0")
            self.assertEqual(comparison["measured_minus_ideal"], str(Fraction(64, 10000)))
            self.assertEqual(comparison["residual_over_quoted_uncertainty"], str(Fraction(64, 120)))
            self.assertEqual(comparison["nuisance_bias"], "unmodeled_not_zero")
            self.assertEqual(comparison["apparatus_prediction"], "not_available")
            self.assertEqual(comparison["empirical_acceptance"], "not_assessed")
            self.assertEqual(scope["candidate_verdict"], "not_assessed")
            self.assertEqual(report["empirical_status"], "published_summary_compared_conditionally")
            self.assertEqual(report["proof_status"], "not_attempted")
            self.assertEqual(report["rejection_scope"], "no_primitive_rejection_descriptive_comparison_only")
            self.assertEqual(report["status"], "no_counterexample_within_bounds")
            self.assertEqual(scope["scientific_status"], "conditional_ideal_null_comparison")
            comparisons.append(comparison)
        self.assertEqual(comparisons[0], comparisons[1])
        self.assertEqual(comparisons[1], comparisons[2])

    def test_published_summary_retains_source_dimensions_and_same_data_discrepancy(self) -> None:
        data = observation.published_summary()
        self.assertEqual(object_fields(data["primary"])["quoted_uncertainty"], "0.0120")
        alternate = object_fields(data["alternative_same_summary"])
        self.assertEqual(alternate["quoted_uncertainty"], "0.0119")
        self.assertIn("do not average", str(alternate["relation"]))
        self.assertEqual(object_fields(data["observable"])["dimension"], "dimensionless")
        self.assertIn("1007.4193v1", str(object_fields(data["source"])["pdf_url"]))
        self.assertEqual(object_fields(data["source"])["pdf_sha256"],
                         "58f815646f439747e81506ce732aa88923451641ea61ed466b3fa885112aa448")
        self.assertIn("1308.2022v2", str(data["limitations"]))
        self.assertIn("Imax normalization is not imported", str(data["limitations"]))
        self.assertIn("not assigned to the HSPS", str(data["limitations"]))
        self.assertIn("no iid Gaussian", str(data["uncertainty_interpretation"]))

    def test_prediction_has_no_measurement_access_and_all_parameters_are_literal(self) -> None:
        with patch.object(observation, "published_summary", side_effect=AssertionError("data leaked")):
            for eta in range(3):
                for product in range(-2, 3):
                    model = AmplitudeAlgebra("literal", "integer_plane", product, eta)
                    prediction = observation.predict_ideal_null(model)
                    self.assertEqual(prediction["ideal_kappa"], "0")
                    self.assertEqual(prediction["eta"], eta)
        order: list[str] = []
        predict = observation.predict_ideal_null
        read = observation.published_summary

        def ordered_predict(model: AmplitudeAlgebra) -> dict[str, object]:
            order.append("predict")
            return predict(model)

        def ordered_read() -> dict[str, object]:
            order.append("read_measurements")
            return read()

        with (patch.object(observation, "predict_ideal_null", side_effect=ordered_predict),
              patch.object(observation, "published_summary", side_effect=ordered_read)):
            run()
        self.assertEqual(order, ["predict", "read_measurements"])

    def test_changed_observation_changes_arithmetic_not_prediction_or_empirical_verdict(self) -> None:
        baseline = object_fields(run()["scope"])
        data = observation.published_summary()
        data["primary"] = {**object_fields(data["primary"]), "value": "1.2345"}
        with patch.object(observation, "published_summary", return_value=data):
            changed = run()
        scope = object_fields(changed["scope"])
        self.assertEqual(scope["prediction"], baseline["prediction"])
        self.assertNotEqual(scope["comparison"], baseline["comparison"])
        self.assertEqual(changed["status"], "no_counterexample_within_bounds")
        self.assertEqual(scope["candidate_verdict"], "not_assessed")

    def test_every_unsupported_control_stays_unsupported_without_reading_measurements(self) -> None:
        expected = {
            "negative": "missing_nonnegative_readout_bridge", "zero": "zero_or_unestablished_denominator",
            "quartic": "missing_preparation_mapping", "absolute": "missing_preparation_mapping",
            "missing_bridge": "missing_or_unknown_explicit_bridge", "unknown_experiment": "unknown_experiment",
            "unbound_source": "missing_exact_reviewed_source_binding",
        }
        with patch.object(observation, "published_summary", side_effect=AssertionError("unsupported read data")):
            for name, reason in expected.items():
                with self.subTest(name=name):
                    report = run(f"observation_{name}")
                    scope = object_fields(report["scope"])
                    self.assertEqual(report["status"], "unsupported")
                    self.assertEqual(report["empirical_status"], "not_tested")
                    self.assertEqual(scope["unsupported_reason"], reason)
                    self.assertEqual(scope["candidate_verdict"], "not_assessed")
                    self.assertNotIn("comparison", scope)
                    self.assertEqual(object_fields(scope["budget"])["checked"], 0)

    def test_no_weight_repair_or_physical_nonlinear_prediction(self) -> None:
        for name, coordinates, expected in (("negative", (0, 1), -1), ("zero", (1, 0), 0),
                                             ("quartic", (2, 0), 16), ("absolute", (-2, 0), 2)):
            model = parse_amplitude_algebra(fixtures()[f"observation_{name}"]["model"])
            self.assertEqual(model.weight(coordinates), expected)
            self.assertEqual(observation.predict_ideal_null(model)["status"], "unsupported")

    def test_eight_context_affine_identity_and_context_dependent_bridge_failure(self) -> None:
        # Independent eight-context inclusion/exclusion, including empty background.
        model = AmplitudeAlgebra("literal", "integer_scalar", 0, 0)
        rates: dict[str, Fraction] = {}
        for context in ("", "A", "B", "C", "AB", "AC", "BC", "ABC"):
            rates[context] = Fraction(3, 2) * model.weight((len(context), 0)) + Fraction(2, 3)
        epsilon = rates["ABC"] - rates["AB"] - rates["AC"] - rates["BC"] + rates["A"] + rates["B"] + rates["C"] - rates[""]
        self.assertEqual(epsilon, 0)
        rates = {key: Fraction(len(key) ** 2) for key in rates}
        rates["ABC"] += 1  # Toy context-dependent detector perturbation breaks the supplied bridge.
        epsilon = rates["ABC"] - rates["AB"] - rates["AC"] - rates["BC"] + rates["A"] + rates["B"] + rates["C"] - rates[""]
        denominator = sum(abs(rates[pair] - rates[pair[0]] - rates[pair[1]] + rates[""])
                          for pair in ("AB", "AC", "BC"))
        self.assertEqual((epsilon, denominator, epsilon / denominator), (1, 6, Fraction(1, 6)))

    def test_one_closed_form_comparison_not_sampled_trials(self) -> None:
        spec = fixtures()["observation_gaussian"]
        first = pipeline.run_batch([spec], Limits(max_cases=1))[0]
        second = pipeline.run_batch([spec], Limits(max_cases=5000, coefficient_radius=2,
                                                   reference_radius=2, max_copies=2))[0]
        self.assertNotEqual(first.key, second.key)
        for result in (first, second):
            checks = result.report["checks"]
            assert isinstance(checks, list)
            check = object_fields(checks[0])
            self.assertEqual((check["checked"], check["planned"]), (1, 1))
            self.assertEqual(check["requirement"], "complete_descriptive_comparison_only")
            self.assertIsNone(check["witness"])
            self.assertEqual(object_fields(result.report["scope"])["unused_limits"],
                             ["coefficient_radius", "reference_radius", "max_copies"])

    def test_strict_candidate_schema_not_expected_answer_or_fitted_input(self) -> None:
        spec = fixtures()["observation_gaussian"]
        for name in ("expected_answer", "value", "quoted_uncertainty", "tolerance", "preparations", "data_path"):
            with self.subTest(name=name), self.assertRaises(ValueError):
                pipeline.run_batch([{**spec, name: "0"}])
        for name in ("id", "experiment", "bridge", "model", "family"):
            changed = {key: value for key, value in spec.items() if key != name}
            with self.subTest(name=name), self.assertRaises((ValueError, TypeError)):
                pipeline.run_batch([changed])
        invalid: list[object] = [None, True, 1, [], {}, "../path", "UPPER"]
        for value in invalid:
            for name in ("experiment", "bridge"):
                with self.subTest(value=value, name=name), self.assertRaises((ValueError, TypeError)):
                    pipeline.run_batch([{**spec, name: value}])
        for model in (spec, pipeline.controls()["qm_born"].specification()):
            with self.assertRaises(ValueError):
                pipeline.run_batch([{**spec, "model": model}])
        for item in fixtures().values():
            self.assertEqual(observation.parse_published_observation(item).specification(), item)

    def test_invalid_published_data_fails_closed_not_candidate_rejection(self) -> None:
        data = observation.published_summary()
        variants = [{**data, "extra": 0}, {**data, "schema": "unknown"},
                    {**data, "id": "unknown"}, {**data, "limitations": []},
                    {**data, "observable": {**object_fields(data["observable"]), "dimension": "count"}}]
        for value in ("0.0000", "-0.0100", "nan", "1/2", 0.012, True, None):
            variants.append({**data, "primary": {**object_fields(data["primary"]), "quoted_uncertainty": value}})
        for variant in variants:
            with (self.subTest(variant=variant), patch.object(observation, "load_json", return_value=variant),
                  self.assertRaises((ValueError, TypeError))):
                run()
        for value in ("0.0000", "-0.0100"):
            with self.assertRaises(ValueError):
                observation.compare_summary(Fraction(0), {"value": "0.0064", "quoted_uncertainty": value,
                                                         "locator": "test"})

    def test_exact_reviewed_sources_only_and_no_snapshot_reinterpretation(self) -> None:
        specs = inventory_specifications(pipeline.ROOT / "data/existing_primitive_inventory.json")
        base = fixtures()["observation_gaussian"]
        for name in ("pair_history_signed_scalar_realization", "pair_history_gaussian_realization"):
            model = next(object_fields(spec) for spec in specs if object_fields(spec)["id"] == name)
            result = pipeline.run_batch([{**base, "model": model}])[0]
            scope = object_fields(result.report["scope"])
            self.assertEqual(scope["execution_status"], "complete")
            self.assertEqual(scope["model_origin"], "exact_archived_source_specification_binding")
            changed = copy.deepcopy(model)
            changed["declared_status"] = "a_different_label"
            report = pipeline.run_batch([{**base, "model": changed}])[0].report
            self.assertEqual(report["status"], "unsupported")

    def test_cache_replay_provenance_and_temp_history(self) -> None:
        specs: list[object] = list(fixtures().values())
        with tempfile.TemporaryDirectory() as directory:
            cache = Path(directory) / "cache"
            history = History(Path(directory) / "history")
            first = record_batch(specs, cache_dir=cache, history=history)
            with patch.object(pipeline, "compute", side_effect=AssertionError("hit executed")):
                cached = pipeline.run_batch(specs, cache_dir=cache)
            fresh = pipeline.run_batch(specs, cache_dir=cache, fresh=True)
            for initial, hit, current in zip(first.results, cached, fresh, strict=True):
                self.assertTrue(hit.reused)
                self.assertEqual(initial.report, hit.report)
                self.assertEqual(initial.report, current.report)
                assert initial.artifact is not None
                self.assertEqual(initial.report, pipeline.replay_artifact(initial.artifact))
            before = {p: p.read_bytes() for p in history.root.rglob("*") if p.is_file()}
            self.assertEqual(recheck_history(history)["status"], "unchanged")
            self.assertEqual(before, {p: p.read_bytes() for p in history.root.rglob("*") if p.is_file()})

    def test_every_new_code_data_and_proof_input_is_keyed_and_stale_loaded_sources_fail(self) -> None:
        spec = fixtures()["observation_gaussian"]
        result = pipeline.run_batch([spec])[0]
        sources = pipeline.provenance()
        self.assertNotIn("PUBLISHED_OBSERVATION_RESULT.md", pipeline.SOURCE_PATHS)
        for path in (observation.DATA_PATH, observation.LEAN_PATH, "theory_experiments/published_observation.py",
                     "lakefile.lean", "lean-toolchain"):
            self.assertIn(path, pipeline.SOURCE_PATHS)
            changed = copy.deepcopy(sources)
            hashes = dict(object_fields(changed["source_sha256"]))
            hashes[path] = "0" * 64
            changed["source_sha256"] = hashes
            key = pipeline.digest(pipeline.request_for(pipeline.parse_hypothesis(spec), Limits(), changed))
            self.assertNotEqual(result.key, key)
            with (patch.object(pipeline, "provenance", return_value=changed),
                  self.assertRaisesRegex(ValueError, "since import")):
                pipeline.run_batch([spec])
        for field in ("id", "experiment", "bridge"):
            changed_spec = {**spec, field: "different_label"}
            self.assertNotEqual(pipeline.run_batch([changed_spec])[0].key, result.key)

    def test_changed_data_bytes_fail_stale_interpreter_then_change_fresh_key(self) -> None:
        data = observation.published_summary()
        spec = fixtures()["observation_gaussian"]
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            path = root / observation.DATA_PATH
            path.parent.mkdir(parents=True)
            path.write_text(canonical_json(data), encoding="utf-8")
            with (patch.object(pipeline, "ROOT", root), patch.object(observation, "ROOT", root),
                  patch.object(pipeline, "SOURCE_PATHS", (observation.DATA_PATH,))):
                with patch.object(pipeline, "LOADED_SOURCE_HASHES", pipeline.provenance()["source_sha256"]):
                    first = pipeline.run_batch([spec])[0]
                    data["primary"] = {**object_fields(data["primary"]), "value": "0.0070"}
                    path.write_text(canonical_json(data), encoding="utf-8")
                    with self.assertRaisesRegex(ValueError, "since import"):
                        pipeline.run_batch([spec])
                with patch.object(pipeline, "LOADED_SOURCE_HASHES", pipeline.provenance()["source_sha256"]):
                    second = pipeline.run_batch([spec])[0]
                self.assertNotEqual(first.key, second.key)
                self.assertEqual(object_fields(first.report["scope"])["prediction"],
                                 object_fields(second.report["scope"])["prediction"])
                self.assertNotEqual(object_fields(first.report["scope"])["comparison"],
                                    object_fields(second.report["scope"])["comparison"])

    def test_existing_family_reports_match_pinned_semantics_without_new_fields(self) -> None:
        history = History()
        # Bounded representative old families; full old history is a separate acceptance check.
        seen: set[str] = set()
        for path in sorted((history.root / "submissions").glob("*.json")):
            saved = history.get("submissions", path.stem)
            old = history.baseline(path.stem)["reports"]
            candidates = saved["candidates"]
            assert isinstance(candidates, list) and isinstance(old, list)
            for spec, report in zip(candidates, old, strict=True):
                family = str(object_fields(spec)["family"])
                if family in seen or family == "published_observation":
                    continue
                seen.add(family)
                request = object_fields(object_fields(report)["request"])
                limits = object_fields(request["limits"])
                current = pipeline.run_batch([spec], parse_limits(limits))[0].report
                self.assertEqual(semantic_report(current), semantic_report(object_fields(report)))
                # Bell adds a scoped empirical test; its pinned semantics remain checked above.
                expected_empirical = ("conditional_statistical_exclusion"
                                      if family == "bell_local_response" else "not_tested")
                self.assertEqual(current["empirical_status"], expected_empirical)
        self.assertIn("universe_bench", seen)

    def test_existing_cli_and_exit_statuses_preserve_descriptive_completion(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            args = ["--batch-file", str(CONTROLS), "--no-cache", "--history-dir", directory, "--json"]
            with redirect_stdout(io.StringIO()) as output:
                self.assertEqual(screen_main(args), 3)
            reports = [object_fields(json.loads(line)) for line in output.getvalue().splitlines()]
            self.assertEqual(len(reports), 10)
            self.assertTrue(all(row["proof_status"] == "not_attempted" for row in reports))
            with redirect_stdout(io.StringIO()), redirect_stderr(io.StringIO()):
                self.assertEqual(screen_main([*args, "--fresh"]), 3)


if __name__ == "__main__":
    unittest.main()
