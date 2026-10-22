"""Independent pair-tensor controls; no fixture success becomes a native derivation."""

from __future__ import annotations

import copy
import hashlib
import io
import json
import tempfile
import unittest
from contextlib import redirect_stderr, redirect_stdout
from pathlib import Path
from unittest.mock import patch

from scripts.check_identical_particles import evidence
from scripts.check_identical_particles import main as audit_main
from scripts.screen_hypotheses import main as screen_main
from theory_experiments import candidate_pipeline as pipeline
from theory_experiments.candidate_history import History, recheck_history, record_batch
from theory_experiments.identical_particles import (
    evaluate_identical_pair,
    parse_identical_pair,
)
from theory_experiments.primitive_screen import (
    Limits,
    load_json,
    object_fields,
)

ROOT = Path(__file__).resolve().parents[1]
CONTROLS = ROOT / "data/identical_particle_controls.json"
SUCCESS = "no_counterexample_within_bounds"


def fixtures() -> dict[str, dict[str, object]]:
    values = load_json(CONTROLS)
    assert isinstance(values, list)
    return {str(object_fields(value)["id"]): object_fields(value) for value in values}


def report_for(name: str, limits: Limits | None = None) -> dict[str, object]:
    return pipeline.run_batch([fixtures()[name]], limits, fresh=True)[0].report


def checks(report: dict[str, object]) -> dict[str, dict[str, object]]:
    values = report["checks"]
    assert isinstance(values, list)
    return {str(object_fields(value)["id"]): object_fields(value) for value in values}


def snapshot(directory: Path) -> dict[str, str]:
    return {str(path.relative_to(directory)): hashlib.sha256(path.read_bytes()).hexdigest()
            for path in directory.rglob("*") if path.is_file()}


class IdenticalParticleTests(unittest.TestCase):
    def test_all_saved_controls_have_independent_expected_outcomes(self) -> None:
        expected = {
            "fermion_same_orbital_different_spin": SUCCESS,
            "fermion_diagonal_violation": "counterexample",
            "fermion_symmetric_zero_diagonal": "counterexample",
            "fermion_imaginary_symmetric": "counterexample",
            "fermion_sparse_four_modes": SUCCESS,
            "boson_occupied_diagonal": SUCCESS,
            "boson_zero_diagonal": SUCCESS,
            "boson_imaginary_symmetric": SUCCESS,
            "boson_antisymmetric_violation": "counterexample",
            "fermion_zero_tensor": "inconclusive",
            "fermion_single_mode_violation": "counterexample",
            "boson_zero_tensor": "inconclusive",
        }
        self.assertEqual(set(fixtures()), set(expected))
        for name, status in expected.items():
            with self.subTest(name=name):
                self.assertEqual(report_for(name)["status"], status)

    def test_pauli_and_exchange_are_independent(self) -> None:
        for name in ("fermion_symmetric_zero_diagonal", "fermion_imaginary_symmetric"):
            result = checks(report_for(name))
            self.assertEqual(result["pauli_same_complete_mode"]["status"], SUCCESS)
            self.assertEqual(result["exchange_symmetry"]["status"], "counterexample")
        self.assertEqual(checks(report_for("fermion_diagonal_violation"))[
            "pauli_same_complete_mode"]["status"], "counterexample")

    def test_imaginary_exchange_uses_transpose_not_dagger(self) -> None:
        result = checks(report_for("fermion_imaginary_symmetric"))["exchange_symmetry"]
        witness = object_fields(result["witness"])
        self.assertEqual(witness["actual"], "2/7")
        inputs = object_fields(witness["inputs"])
        self.assertEqual(inputs["component"], "imaginary")
        self.assertEqual(inputs["complex_residual"], ["0", "2/7"])
        self.assertEqual(report_for("boson_imaginary_symmetric")["status"], SUCCESS)

    def test_opposite_residual_components_do_not_cancel(self) -> None:
        spec = fixtures()["fermion_symmetric_zero_diagonal"]
        spec["amplitudes"] = [[["0", "0"], ["1", "-1"]], [["0", "0"], ["0", "0"]]]
        result = checks(pipeline.run_batch([spec])[0].report)["exchange_symmetry"]
        self.assertEqual(result["status"], "counterexample")
        self.assertEqual(object_fields(object_fields(result["witness"])["inputs"])[
            "complex_residual"], ["1", "-1"])

    def test_opposite_diagonal_residuals_do_not_cancel(self) -> None:
        spec = fixtures()["fermion_symmetric_zero_diagonal"]
        spec["amplitudes"] = [[["1", "0"], ["0", "0"]], [["0", "0"], ["-1", "0"]]]
        self.assertEqual(checks(pipeline.run_batch([spec])[0].report)[
            "pauli_same_complete_mode"]["status"], "counterexample")

    def test_complete_mode_includes_internal_label(self) -> None:
        model = parse_identical_pair(fixtures()["fermion_same_orbital_different_spin"])
        self.assertEqual(model.modes, (("s", "up"), ("s", "down")))
        self.assertEqual(report_for(model.id)["status"], SUCCESS)
        duplicate = model.specification()
        duplicate["modes"] = [{"orbital": "s", "internal": "up"}] * 2
        with self.assertRaisesRegex(ValueError, "duplicate complete mode"):
            parse_identical_pair(duplicate)

    def test_sparse_unnormalized_state_needs_no_all_pairs_occupancy(self) -> None:
        report = report_for("fermion_sparse_four_modes")
        result = checks(report)
        self.assertEqual(report["status"], SUCCESS)
        self.assertEqual(result["exchange_symmetry"]["checked"], 20)
        self.assertEqual(result["pauli_same_complete_mode"]["checked"], 8)
        self.assertEqual(object_fields(report["scope"])["normalization"],
            "not_required_for_homogeneous_identities_no_probability_readout")

    def test_boson_pauli_is_not_applicable_never_a_successful_check(self) -> None:
        for name in ("boson_occupied_diagonal", "boson_zero_diagonal", "boson_zero_tensor"):
            report = report_for(name)
            self.assertNotIn("pauli_same_complete_mode", checks(report))
            applicability = object_fields(object_fields(report["scope"])["requirement_applicability"])
            self.assertEqual(applicability["pauli_same_complete_mode"], "not_applicable")

    def test_zero_tensor_is_inconclusive_not_vacuum_rejection(self) -> None:
        for name in ("fermion_zero_tensor", "boson_zero_tensor"):
            report = report_for(name)
            self.assertEqual(report["status"], "inconclusive")
            self.assertEqual(checks(report)["nonzero_prepared_two_particle_state"]["status"], "inconclusive")
            meaning = object_fields(report["scope"])["zero_tensor_meaning"]
            assert isinstance(meaning, str)
            self.assertIn("not_global_vacuum_rejection", meaning)

    def test_limits_never_report_full_success_after_truncation(self) -> None:
        spec = parse_identical_pair(fixtures()["fermion_sparse_four_modes"])
        for budget in (1, 7, 8, 19):
            result, _ = evaluate_identical_pair(spec, Limits(max_cases=budget))
            exchange = {check.id: check for check in result}["exchange_symmetry"]
            self.assertEqual(exchange.checked, budget)
            self.assertEqual(exchange.planned, 20)
            self.assertEqual(exchange.status, "inconclusive")
            self.assertEqual(report_for(spec.id, Limits(max_cases=budget))["status"], "inconclusive")

    def test_one_mode_cases_do_not_assert_fermion_preparation_exists(self) -> None:
        self.assertEqual(report_for("fermion_zero_tensor")["status"], "inconclusive")
        self.assertEqual(report_for("fermion_single_mode_violation")["status"], "counterexample")
        self.assertEqual(report_for("boson_occupied_diagonal")["status"], SUCCESS)

    def test_round_trip_and_bounded_exact_rationals(self) -> None:
        for spec in fixtures().values():
            model = parse_identical_pair(spec)
            self.assertEqual(parse_identical_pair(model.specification()), model)
        spec = fixtures()["boson_occupied_diagonal"]
        spec["amplitudes"] = [[["-999999999999/999999999998", "1/999999999999"]]]
        self.assertEqual(pipeline.run_batch([spec])[0].report["status"], SUCCESS)

    def test_malformed_numbers_are_invalid_input_not_counterexamples(self) -> None:
        malformed: list[object] = [True, False, 0, 0.5, "1.0", "1/0", "1/0002", "1000000000000",
                                   "1/1000000000000", "NaN", "inf", None, {}, []]
        for value in malformed:
            spec = fixtures()["boson_occupied_diagonal"]
            spec["amplitudes"] = [[[value, "0"]]]
            with self.subTest(value=value), self.assertRaises((TypeError, ValueError)):
                parse_identical_pair(spec)

    def test_malformed_dimensions_modes_and_origin_are_rejected(self) -> None:
        base = fixtures()["boson_occupied_diagonal"]
        malformed: list[dict[str, object]] = [
            {**base, "modes": []}, {**base, "modes": [{"orbital": "s", "internal": "up"}] * 5},
            {**base, "modes": [{"orbital": "s"}]}, {**base, "modes": [True]},
            {**base, "modes": [{"orbital": True, "internal": "up"}]},
            {**base, "modes": [{"orbital": "s", "internal": "up", "extra": "x"}]},
            {**base, "modes": [{"orbital": "s", "internal": "x" * 65}]},
            {**base, "amplitudes": []}, {**base, "amplitudes": [[["0", "0"]], [["0", "0"]]]},
            {**base, "amplitudes": [[[]]]}, {**base, "amplitudes": [["1"]]},
            {**base, "amplitudes": True}, {**base, "statistics": "anyons"},
            {**base, "origin": "native_prediction"}, {**base, "origin": True},
            {**base, "id": True}, {**base, "extra": "unknown"},
        ]
        missing = dict(base)
        missing.pop("origin")
        malformed.append(missing)
        for spec in malformed:
            with self.subTest(spec=spec), self.assertRaises((TypeError, ValueError)):
                parse_identical_pair(spec)

    def test_dispatch_provenance_and_evidence_boundaries(self) -> None:
        report = report_for("fermion_same_orbital_different_spin")
        hashes = object_fields(object_fields(object_fields(report["request"])["provenance"])["source_sha256"])
        self.assertIn("theory_experiments/identical_particles.py", hashes)
        self.assertIn("scripts/check_identical_particles.py", hashes)
        self.assertEqual(report["proof_status"], "not_attempted")
        self.assertEqual(report["empirical_status"], "not_tested")
        self.assertEqual(object_fields(report["scope"])["scientific_status"], "unassessed")

    def test_new_family_cache_replays_and_rejects_changed_engine_hash(self) -> None:
        spec = fixtures()["fermion_same_orbital_different_spin"]
        with tempfile.TemporaryDirectory() as directory:
            cache = Path(directory) / "cache"
            initial = pipeline.run_batch([spec], cache_dir=cache)[0]
            reused = pipeline.run_batch([spec], cache_dir=cache)[0]
            fresh = pipeline.run_batch([spec], cache_dir=cache, fresh=True)[0]
            self.assertFalse(initial.reused)
            self.assertTrue(reused.reused)
            self.assertFalse(fresh.reused)
            self.assertEqual(initial.report, reused.report)
            self.assertEqual(initial.report, fresh.report)
            self.assertIsNotNone(initial.artifact)
            assert initial.artifact is not None
            self.assertEqual(pipeline.replay_artifact(initial.artifact), initial.report)
            changed = copy.deepcopy(pipeline.provenance())
            hashes = object_fields(changed["source_sha256"])
            hashes["theory_experiments/identical_particles.py"] = "0" * 64
            changed["source_sha256"] = hashes
            before = snapshot(cache)
            with patch.object(pipeline, "provenance", return_value=changed), self.assertRaisesRegex(
                    ValueError, "sources changed since import"):
                pipeline.run_batch([spec], cache_dir=cache)
            self.assertEqual(snapshot(cache), before)

    def test_new_controls_are_retained_and_replayed_without_rewriting_history(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            history = History(Path(directory) / "history")
            run = record_batch(list(fixtures().values()), history=history, fresh=True)
            before = snapshot(history.root)
            replay = recheck_history(history)
            self.assertEqual(replay["candidates"], 12)
            self.assertEqual(replay["status"], "unchanged")
            self.assertEqual(replay["errors"], [])
            self.assertEqual(before, snapshot(history.root))
            self.assertTrue(any(name.endswith(".json.gz") for name in before))
            self.assertEqual(history.baseline(run.submission)["reports"], [r.report for r in run.results])

    def test_audit_missing_adapters_never_changes_original_candidates(self) -> None:
        review = object_fields(load_json(ROOT / "data/native_observability_review.json"))["candidates"]
        assert isinstance(review, list)
        original = copy.deepcopy(review)
        result = evidence(review + [pipeline.controls()["qm_born"].specification()])
        rows = result["reports"]
        assert isinstance(rows, list)
        for value in rows:
            row = object_fields(value)
            self.assertEqual(row["status"], "unsupported")
            self.assertEqual(row["candidate_verdict"], "unchanged")
            self.assertEqual(row["scientific_status"], "unassessed")
        self.assertEqual(review, original)

    def test_audit_boson_applicability_and_cli_exit_codes(self) -> None:
        result = evidence([fixtures()["boson_occupied_diagonal"]])
        rows = result["reports"]
        assert isinstance(rows, list)
        self.assertEqual(object_fields(object_fields(object_fields(rows[0])["scope"])[
            "requirement_applicability"])["pauli_same_complete_mode"], "not_applicable")
        with redirect_stdout(io.StringIO()):
            self.assertEqual(audit_main(["--batch-file", str(CONTROLS)]), 1)
        for specs, expected in (([fixtures()["boson_occupied_diagonal"]], 0),
                                ([pipeline.controls()["qm_born"].specification()], 3),
                                ([fixtures()["fermion_zero_tensor"]], 3)):
            with patch("scripts.check_identical_particles.load_json", return_value=specs), redirect_stdout(io.StringIO()):
                self.assertEqual(audit_main(["--batch-file", "unused.json"]), expected)

    def test_audit_and_cli_are_read_only_even_for_compressed_history(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            history = History(Path(directory) / "history")
            record_batch(list(fixtures().values()), history=history, fresh=True)
            before = snapshot(history.root)
            with redirect_stdout(io.StringIO()):
                self.assertEqual(audit_main(["--batch-file", str(CONTROLS)]), 1)
            self.assertEqual(before, snapshot(history.root))

    def test_cli_no_cache_retains_history_but_creates_no_cache(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            history = Path(directory) / "history"
            with redirect_stdout(io.StringIO()) as output:
                code = screen_main(["--batch-file", str(CONTROLS), "--no-cache", "--history-dir", str(history)])
            self.assertEqual(code, 1)
            rows = [object_fields(json.loads(line)) for line in output.getvalue().splitlines()]
            self.assertEqual(len(rows), 12)
            self.assertTrue(all(row["artifact"] is None and row["reused"] is False for row in rows))
            self.assertEqual({path.name for path in Path(directory).iterdir()}, {"history"})
            self.assertEqual(len(list((history / "submissions").glob("*.json"))), 1)
            self.assertEqual(len(list((history / "observations").glob("*.json.gz"))), 1)

    def test_invalid_cli_input_exits_two_without_candidate_rejection(self) -> None:
        with patch("scripts.check_identical_particles.load_json", return_value={}), redirect_stderr(io.StringIO()):
            self.assertEqual(audit_main(["--batch-file", "unused.json"]), 2)


if __name__ == "__main__":
    unittest.main()
