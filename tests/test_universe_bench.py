"""Independent finite software oracles, never physical model-selection targets."""

from __future__ import annotations

import copy
import hashlib
import io
import json
import os
import subprocess
import sys
import tempfile
import unittest
from contextlib import redirect_stderr, redirect_stdout
from pathlib import Path
from unittest.mock import patch

from scripts.archive_existing_primitives import inventory_specifications
from scripts.check_identical_particles import evidence as pair_audit
from scripts.check_native_observability import evidence as native_audit
from scripts.screen_hypotheses import main as screen_main
from theory_experiments import candidate_pipeline as pipeline
from theory_experiments.amplitude_algebra import SOURCE_BINDINGS, AmplitudeAlgebra
from theory_experiments.candidate_history import History, recheck_history, record_batch
from theory_experiments.native_observability import analyze_projection
from theory_experiments.native_operations import analyze_operation
from theory_experiments.primitive_screen import (
    Limits,
    canonical_json,
    load_json,
    object_fields,
)
from theory_experiments.universe_bench import AMPLITUDE_FIELDS, parse_universe_bench

ROOT = Path(__file__).resolve().parents[1]
CONTROLS = ROOT / "data/universe_bench_controls.json"
SUCCESS = "no_counterexample_within_bounds"


def fixtures() -> dict[str, dict[str, object]]:
    values = load_json(CONTROLS)
    assert isinstance(values, list)
    return {str(object_fields(value)["id"]): object_fields(value) for value in values}


def report_for(name: str = "bench_gaussian_common", budget: int = 1000) -> dict[str, object]:
    return pipeline.run_batch([fixtures()[name]], Limits(max_cases=budget), fresh=True)[0].report


def rows(value: object) -> list[dict[str, object]]:
    assert isinstance(value, list)
    return [object_fields(item) for item in value]


def diagnostics(report: dict[str, object]) -> list[dict[str, object]]:
    return rows(object_fields(report["scope"])["completed_preparations"])


def snapshot(directory: Path) -> dict[str, str]:
    return {str(path.relative_to(directory)): hashlib.sha256(path.read_bytes()).hexdigest()
            for path in directory.rglob("*") if path.is_file()}


class UniverseBenchTests(unittest.TestCase):
    def test_all_saved_controls_match_independent_literal_oracles(self) -> None:
        # Constants here are software oracles, never inputs accepted by the engine.
        expected = {
            "bench_scalar_common": [("4", "1", "1", "2"), ("0", "1", "1", "-2")],
            "bench_gaussian_common": [("4", "1", "1", "2"), ("0", "1", "1", "-2")],
            "bench_dual_common": [("4", "1", "1", "2"), ("0", "1", "1", "-2")],
            "bench_scalar_nonreal": [],
            "bench_gaussian_nonreal": [("0", "1", "1", "-2")],
            "bench_dual_nonreal": [("1", "1", "0", "0")],
            "bench_quartic": [("16", "1", "1", "14")],
            "bench_zero": [("0", "0", "0", "0")],
            "bench_negative_weight": [("-4", "-1", "-1", "-2")],
            "bench_absolute": [("2", "1", "1", "0")],
        }
        self.assertEqual(set(fixtures()), set(expected))
        for name, values in expected.items():
            with self.subTest(name=name):
                report = report_for(name)
                self.assertEqual(report["status"], "unsupported" if name == "bench_scalar_nonreal" else SUCCESS)
                actual = []
                for item in diagnostics(report):
                    weights = object_fields(item["raw_weights"])
                    actual.append((weights["both"], weights["left_only"], weights["right_only"],
                                   item["interference_residual"]))
                self.assertEqual(actual, values)

    def test_common_protocol_is_identical_across_three_models(self) -> None:
        reports = [report_for(f"bench_{name}_common") for name in ("scalar", "gaussian", "dual")]
        specs = fixtures()
        preparations = [specs[f"bench_{name}_common"]["preparations"] for name in ("scalar", "gaussian", "dual")]
        self.assertEqual(preparations[0], preparations[1])
        self.assertEqual(preparations[1], preparations[2])
        self.assertEqual(diagnostics(reports[0]), diagnostics(reports[1]))
        self.assertEqual(diagnostics(reports[1]), diagnostics(reports[2]))

    def test_trace_dependencies_inputs_factors_and_origins_are_retained(self) -> None:
        scope = object_fields(report_for("bench_gaussian_nonreal")["scope"])
        trace = rows(scope["trace"])
        self.assertEqual([step["step"] for step in trace], list(range(1, 10)))
        self.assertEqual([step["operation"] for step in trace], [
            "prepare_left", "prepare_right", "multiply_left", "multiply_right", "add_paths",
            "weight_both", "weight_left_only", "weight_right_only", "subtract_blocked_weights"])
        seen: set[str] = set()
        for step in trace:
            dependencies = step["dependencies"]
            assert isinstance(dependencies, list)
            self.assertTrue(all(dependency in seen for dependency in dependencies))
            seen.add(str(step["id"]))
        self.assertEqual(trace[3]["output"], [-1, 0])
        self.assertEqual(object_fields(trace[3]["inputs"])["factor"], [0, 1])
        self.assertEqual(object_fields(trace[3]["inputs"])["amplitude"], [0, 1])
        self.assertEqual(trace[4]["output"], [0, 0])
        self.assertEqual(trace[0]["result_origin"], "supplied")
        self.assertTrue(all(step["result_origin"] == "conditionally_computed" for step in trace[2:]))
        self.assertEqual(scope["candidate_verdict"], "unchanged")
        self.assertEqual(scope["execution_status"], "complete")

    def test_step_budget_stops_model_operations_before_the_next_step(self) -> None:
        complete = rows(object_fields(report_for()["scope"])["trace"])
        for budget in range(1, 19):
            with (
                self.subTest(budget=budget),
                patch.object(AmplitudeAlgebra, "multiply", autospec=True, side_effect=AmplitudeAlgebra.multiply) as multiply,
                patch.object(AmplitudeAlgebra, "add", autospec=True, side_effect=AmplitudeAlgebra.add) as add,
                patch.object(AmplitudeAlgebra, "weight", autospec=True, side_effect=AmplitudeAlgebra.weight) as weight,
            ):
                report = report_for(budget=budget)
                scope = object_fields(report["scope"])
                trace = rows(scope["trace"])
                self.assertEqual(trace, complete[:budget])
                self.assertEqual(multiply.call_count, sum(step["operation"] in ("multiply_left", "multiply_right")
                                                         for step in trace))
                self.assertEqual(add.call_count, sum(step["operation"] == "add_paths" for step in trace))
                self.assertEqual(weight.call_count, sum(str(step["operation"]).startswith("weight_") for step in trace))
                self.assertEqual(report["status"], SUCCESS if budget == 18 else "inconclusive")
                self.assertEqual(scope["execution_status"], "complete" if budget == 18 else "incomplete")
                self.assertEqual(len(diagnostics(report)), budget // 9)
                check = rows(report["checks"])[0]
                self.assertEqual((check["checked"], check["planned"]), (budget, 18))
                self.assertEqual(check["id"], "two_path_execution_completion_only")

    def test_independent_oracle_detects_mutated_native_weight(self) -> None:
        with patch.object(AmplitudeAlgebra, "weight", return_value=7):
            mutated = report_for("bench_gaussian_nonreal")
        # Completion does not turn into a hidden scientific target gate.
        self.assertEqual(mutated["status"], SUCCESS)
        with self.assertRaises(AssertionError):
            self.assertEqual(object_fields(diagnostics(mutated)[0]["raw_weights"])["both"], "0")

    def test_independently_expanded_gaussian_and_dual_products(self) -> None:
        for name, k, eta in (("bench_gaussian_nonreal", -1, 1), ("bench_dual_nonreal", 0, 0)):
            spec = fixtures()[name]
            spec["preparations"] = [{"id": "expanded", "left": [-2, 1], "right": [1, 2],
                                     "left_factor": [2, -1], "right_factor": [-1, -2]}]
            # Expanded by hand from (a+b*u)(c+d*u), with u^2=k.
            left, right = (-4 - k, 4), (-1 - 4 * k, -4)
            both = (left[0] + right[0]) ** 2 + eta * (left[1] + right[1]) ** 2
            blocked = (left[0] ** 2 + eta * left[1] ** 2, right[0] ** 2 + eta * right[1] ** 2)
            report = pipeline.run_batch([spec])[0].report
            result = diagnostics(report)[0]
            self.assertEqual(result["raw_weights"], {"both": str(both), "left_only": str(blocked[0]),
                                                     "right_only": str(blocked[1])})
            self.assertEqual(result["interference_residual"], str(both - sum(blocked)))
            trace = rows(object_fields(report["scope"])["trace"])
            self.assertEqual(trace[2]["output"], list(left))
            self.assertEqual(trace[3]["output"], list(right))

    def test_bad_scalar_coordinates_preflight_every_field_without_executing(self) -> None:
        for field in AMPLITUDE_FIELDS:
            spec = fixtures()["bench_scalar_common"]
            preps = rows(spec["preparations"])
            preps[1][field] = [0, 1]
            spec["preparations"] = preps
            with self.subTest(field=field), patch.object(AmplitudeAlgebra, "multiply", side_effect=AssertionError("ran")):
                report = pipeline.run_batch([spec])[0].report
            scope = object_fields(report["scope"])
            self.assertEqual(report["status"], "unsupported")
            self.assertEqual(scope["trace"], [])
            self.assertEqual(scope["completed_preparations"], [])
            self.assertEqual(scope["candidate_verdict"], "unchanged")
            self.assertEqual(scope["unsupported_reason"], {"kind": "outside_integer_scalar_carrier",
                "preparation": "opposite", "field": field, "amplitude": [0, 1]})

    def test_unknown_valid_scenario_is_unsupported_without_executing(self) -> None:
        spec = fixtures()["bench_gaussian_common"]
        spec["scenario"] = "unknown_v2"
        with patch.object(AmplitudeAlgebra, "multiply", side_effect=AssertionError("ran")):
            report = pipeline.run_batch([spec])[0].report
        self.assertEqual(report["status"], "unsupported")
        self.assertEqual(object_fields(report["scope"])["unsupported_reason"],
                         {"kind": "scenario_mapping", "scenario": "unknown_v2"})

    def test_exact_two_source_bindings_and_original_open_bridges(self) -> None:
        sources = [object_fields(spec) for spec in inventory_specifications()]
        known = [source for source in sources if pipeline.digest(source) in SOURCE_BINDINGS]
        self.assertEqual(len(known), 2)
        for source in known:
            spec = fixtures()["bench_gaussian_common"]
            spec["model"] = source
            with patch.object(pipeline, "evaluate_qm", side_effect=AssertionError("imported QM")):
                report = pipeline.run_batch([spec])[0].report
            scope = object_fields(report["scope"])
            self.assertEqual(report["status"], SUCCESS)
            self.assertEqual(scope["model_origin"], "exact_archived_source_specification_binding")
            self.assertEqual(scope["model_sha256"], pipeline.digest(source))
            self.assertEqual(scope["source_specification_sha256"], pipeline.digest(source))
            self.assertEqual(scope["source_missing_bridges"], source["missing_bridges"])
            self.assertEqual(object_fields(object_fields(report["request"])["candidate"])["model"], source)
            changed = copy.deepcopy(source)
            changed["declared_status"] = "modified"
            spec["model"] = changed
            modified = pipeline.run_batch([spec])[0].report
            self.assertEqual(modified["status"], "unsupported")
            changed_scope = object_fields(modified["scope"])
            self.assertEqual(changed_scope["model_origin"], "unbound_source_snapshot")
            self.assertNotIn("source_specification_sha256", changed_scope)
            self.assertEqual(changed_scope["source_missing_bridges"], source["missing_bridges"])
        lower = next(source for source in sources if source["id"] == "pair_history_lower_law")
        spec["model"] = lower
        report = pipeline.run_batch([spec])[0].report
        self.assertEqual(report["status"], "unsupported")
        self.assertEqual(object_fields(report["scope"])["model_origin"], "unbound_source_snapshot")

    def test_round_trip_bounds_and_maximum_report_size(self) -> None:
        for spec in fixtures().values():
            bench = parse_universe_bench(spec)
            self.assertEqual(bench.specification(), spec)
            self.assertEqual(parse_universe_bench(bench.specification()), bench)
        spec = fixtures()["bench_gaussian_nonreal"]
        prep = rows(spec["preparations"])[0]
        spec["preparations"] = [{**prep, "id": f"case_{index}"} for index in range(16)]
        report = pipeline.run_batch([spec])[0].report
        self.assertEqual(rows(report["checks"])[0]["planned"], 144)
        self.assertEqual(len(rows(object_fields(report["scope"])["trace"])), 144)
        self.assertLess(len(canonical_json(report).encode("utf-8")), 524288)

    def test_invalid_numbers_shapes_unknown_fields_and_duplicate_ids_are_errors(self) -> None:
        base = fixtures()["bench_gaussian_common"]
        invalid: list[dict[str, object]] = [
            {**base, "expected_answer": 4}, {**base, "scenario": "two path"},
            {**base, "preparations": []}, {**base, "preparations": "not_array"},
        ]
        prep = rows(base["preparations"])[0]
        invalid.append({**base, "preparations": [prep, prep]})
        invalid.append({**base, "preparations": [{**prep, "id": f"case_{index}"} for index in range(17)]})
        for value in (True, 0.5, "1/2", "1", 3, -3, None):
            invalid.append({**base, "preparations": [{**prep, "left": [value, 0]}]})
        for shape_value in ([1], [1, 0, 0], 1, None):
            invalid.append({**base, "preparations": [{**prep, "right_factor": shape_value}]})
        invalid.append({**base, "preparations": [{**prep, "expected_answer": 4}]})
        invalid.append({**base, "model": {**object_fields(base["model"]), "extra": 1}})
        invalid.append({**base, "model": base})
        invalid.append({**base, "model": pipeline.controls()["qm_born"].specification()})
        for spec in invalid:
            with self.subTest(spec=spec), self.assertRaises((ValueError, TypeError)):
                pipeline.run_batch([spec])
        for budget in (0, 5001, True):
            with self.assertRaises(ValueError):
                Limits(max_cases=budget)

    def test_unused_limits_change_request_not_execution(self) -> None:
        spec = fixtures()["bench_gaussian_common"]
        first = pipeline.run_batch([spec], Limits(coefficient_radius=1, reference_radius=1, max_copies=1))[0]
        second = pipeline.run_batch([spec], Limits(coefficient_radius=2, reference_radius=2, max_copies=2))[0]
        self.assertNotEqual(first.key, second.key)
        self.assertEqual(first.report["scope"], second.report["scope"])
        self.assertEqual(object_fields(first.report["scope"])["unused_limits"],
                         ["coefficient_radius", "reference_radius", "max_copies"])

    def test_full_report_cache_fresh_replay_and_canonical_repeatability(self) -> None:
        specs: list[object] = list(fixtures().values())
        with tempfile.TemporaryDirectory() as directory:
            initial = pipeline.run_batch(specs, cache_dir=Path(directory))
            with patch.object(pipeline, "compute", side_effect=AssertionError("cache executed")):
                cached = pipeline.run_batch(specs, cache_dir=Path(directory))
            fresh = pipeline.run_batch(specs, cache_dir=Path(directory), fresh=True)
            for first, second, third in zip(initial, cached, fresh, strict=True):
                self.assertTrue(second.reused)
                self.assertEqual(canonical_json(first.report), canonical_json(second.report))
                self.assertEqual(canonical_json(first.report), canonical_json(third.report))
                assert first.artifact is not None
                self.assertEqual(canonical_json(first.report), canonical_json(pipeline.replay_artifact(first.artifact)))
                self.assertEqual(set(first.report), {"request", "status", "checks", "scope", "arithmetic",
                    "evidence_kind", "proof_status", "empirical_status", "rejection_scope"})

    def test_fresh_process_hash_seed_does_not_change_canonical_full_report(self) -> None:
        program = ("from pathlib import Path; from theory_experiments.candidate_pipeline import run_batch; "
                   "from theory_experiments.primitive_screen import load_json,canonical_json; "
                   "print(canonical_json([r.report for r in run_batch(load_json("
                   "Path('data/universe_bench_controls.json')))]))")
        outputs = [subprocess.run([sys.executable, "-c", program], cwd=ROOT, check=True,
                                  capture_output=True, text=True, env={**os.environ, "PYTHONHASHSEED": seed}).stdout
                   for seed in ("1", "743")]
        self.assertEqual(outputs[0], outputs[1])
        reports = [result.report for result in pipeline.run_batch(list(fixtures().values()))]
        self.assertEqual(outputs[0].strip(), canonical_json(reports))

    def test_key_binds_model_scenario_preparation_and_budget(self) -> None:
        spec = fixtures()["bench_gaussian_common"]
        variants = [spec, {**spec, "scenario": "unimplemented"}]
        altered = copy.deepcopy(spec)
        altered["model"] = {**object_fields(altered["model"]), "weight_rule": "quartic"}
        variants.append(altered)
        altered = copy.deepcopy(spec)
        preps = rows(altered["preparations"])
        preps[0]["left_factor"] = [2, 0]
        altered["preparations"] = preps
        variants.append(altered)
        keys = [pipeline.run_batch([item])[0].key for item in variants]
        keys.append(pipeline.run_batch([spec], Limits(max_cases=1))[0].key)
        self.assertEqual(len(set(keys)), 5)
        self.assertIn("theory_experiments/universe_bench.py", pipeline.SOURCE_PATHS)
        self.assertNotIn("UNIVERSE_BENCH_RESULT.md", pipeline.SOURCE_PATHS)

    def test_stale_source_guards_cover_cache_and_replay(self) -> None:
        spec = fixtures()["bench_gaussian_common"]
        with tempfile.TemporaryDirectory() as directory:
            first = pipeline.run_batch([spec], cache_dir=Path(directory))[0]
            assert first.artifact is not None
            with patch.object(pipeline, "LOADED_SOURCE_HASHES", {}):
                with self.assertRaisesRegex(ValueError, "since import"):
                    pipeline.run_batch([spec], cache_dir=Path(directory))
                with self.assertRaisesRegex(ValueError, "sources/runtime/request differ"):
                    pipeline.replay_artifact(first.artifact)
            source = pipeline.provenance()
            changed = {**source, "source_sha256": {"changed": "universe_bench"}}
            with (patch.object(pipeline, "provenance", side_effect=[source, changed]),
                  self.assertRaisesRegex(ValueError, "during batch")):
                pipeline.run_batch([spec])

    def test_history_append_recheck_and_read_only_gzip_evidence(self) -> None:
        specs: list[object] = list(fixtures().values())
        with tempfile.TemporaryDirectory() as directory:
            history = History(Path(directory) / "history")
            initial = record_batch(specs, history=history, fresh=True)
            before = snapshot(history.root)
            self.assertEqual(len(before), 3)
            saved = history.get("observations", initial.observation)
            self.assertEqual(len(rows(saved["reports"])), 10)
            rechecked = recheck_history(history)
            self.assertEqual(rechecked["status"], "unchanged")
            self.assertEqual(rechecked["candidates"], 10)
            self.assertEqual(snapshot(history.root), before)
            repeated = record_batch(specs, history=history, fresh=True)
            self.assertEqual(initial.observation, repeated.observation)
            self.assertEqual(snapshot(history.root), before)

    def test_invalid_input_retained_as_error_not_countermodel(self) -> None:
        spec = {**fixtures()["bench_gaussian_common"], "expected_answer": 4}
        with tempfile.TemporaryDirectory() as directory:
            history = History(Path(directory))
            with self.assertRaises(ValueError):
                record_batch([spec], history=history)
            submissions = list((history.root / "submissions").glob("*.json"))
            observations = list((history.root / "observations").glob("*.json.gz"))
            self.assertEqual((len(submissions), len(observations)), (1, 1))
            saved = history.get("observations", observations[0].name.removesuffix(".json.gz"))
            self.assertEqual(saved["reports"], [])
            self.assertIsInstance(saved["execution_error"], str)

    def test_downstream_audits_are_unsupported_and_history_read_only(self) -> None:
        spec = fixtures()["bench_gaussian_common"]
        history = ROOT / "data/candidate_history"
        before = snapshot(history)
        self.assertEqual(analyze_projection(spec)["status"], "unsupported")
        operation = {"id": "identity", "kind": "integer_matrix", "matrix": [[1, 0], [0, 1]]}
        self.assertEqual(analyze_operation(spec, operation)["status"], "unsupported")
        for report in (native_audit([spec]), native_audit([spec], [operation]), pair_audit([spec])):
            row = rows(report["reports"])[0]
            self.assertEqual(row["status"], "unsupported")
            self.assertEqual(row["candidate_verdict"], "unchanged")
        self.assertEqual(snapshot(history), before)

    def test_cli_uses_existing_full_report_card_exit_and_replay_contract(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            cache = Path(directory) / "cache"
            history = Path(directory) / "history"
            args = ["--batch-file", str(CONTROLS), "--history-dir", str(history), "--cache-dir", str(cache)]
            with redirect_stdout(io.StringIO()) as output:
                self.assertEqual(screen_main(args), 3)
            cards = [object_fields(json.loads(line)) for line in output.getvalue().splitlines()]
            self.assertEqual(len(cards), 10)
            self.assertEqual(rows(cards[0]["checks"])[0]["id"], "two_path_execution_completion_only")
            before = snapshot(history)
            with redirect_stdout(io.StringIO()) as output:
                self.assertEqual(screen_main([*args, "--json", "--fresh"]), 3)
            full = object_fields(json.loads(output.getvalue().splitlines()[0]))
            self.assertIn("trace", object_fields(full["scope"]))
            with redirect_stdout(io.StringIO()) as output:
                self.assertEqual(screen_main(["--replay", str(cards[0]["artifact"]), "--json"]), 0)
            replay = object_fields(json.loads(output.getvalue()))
            self.assertEqual(replay["scope"], full["scope"])
            self.assertEqual(snapshot(history), before)

    def test_duplicate_json_keys_are_input_errors_before_model_execution(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            path = Path(directory) / "bad.json"
            # A bounded malformed test file, not production candidate code.
            path.write_text('[{"id":"first","id":"second"}]', encoding="utf-8")
            with redirect_stderr(io.StringIO()), redirect_stdout(io.StringIO()):
                self.assertEqual(screen_main(["--batch-file", str(path), "--history-dir", str(Path(directory) / "history")]), 2)

    def test_scientific_boundaries_stay_explicit_for_every_outcome(self) -> None:
        reports = [report_for(), report_for(budget=1), report_for("bench_scalar_nonreal")]
        for report in reports:
            self.assertEqual(report["proof_status"], "not_attempted")
            self.assertEqual(report["empirical_status"], "not_tested")
            scope = object_fields(report["scope"])
            self.assertEqual(scope["scientific_status"], "unassessed")
            self.assertEqual(scope["candidate_verdict"], "unchanged")
            self.assertIn("not_probability", str(scope["weight_meaning"]))
            supplied = object_fields(scope["origins"])["supplied"]
            assert isinstance(supplied, list)
            self.assertIn("weight_rule", supplied)
            check = rows(report["checks"])[0]
            self.assertEqual(check["requirement"], "complete_supplied_protocol_execution_only")
            self.assertIsNone(check["witness"])
            self.assertNotEqual(report["status"], "counterexample")


if __name__ == "__main__":
    unittest.main()
