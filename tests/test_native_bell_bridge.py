"""Independent exact software oracles; no physical model-selection targets."""

from __future__ import annotations

import copy
import json
import tempfile
import unittest
from fractions import Fraction
from pathlib import Path
from unittest.mock import patch

from theory_experiments import candidate_pipeline as pipeline
from theory_experiments.amplitude_algebra import AmplitudeAlgebra
from theory_experiments.native_bell_bridge import parse_native_bell_bridge
from theory_experiments.native_operations import analyze_operation
from theory_experiments.primitive_screen import Limits, load_json, object_fields

ROOT = Path(__file__).resolve().parents[1]
SUCCESS = "no_counterexample_within_bounds"


def fixtures() -> dict[str, dict[str, object]]:
    raw = load_json(ROOT / "data/native_bell_bridge_controls.json")
    assert isinstance(raw, list)
    return {str(object_fields(item)["id"]): object_fields(item) for item in raw}


def report_for(name: str = "native_bell_gaussian_witness", *, spec: dict[str, object] | None = None,
               budget: int = 4) -> dict[str, object]:
    return pipeline.run_batch([fixtures()[name] if spec is None else spec], Limits(max_cases=budget))[0].report


def scope(report: dict[str, object]) -> dict[str, object]:
    return object_fields(report["scope"])


def rows(value: object) -> list[dict[str, object]]:
    assert isinstance(value, list)
    return [object_fields(item) for item in value]


def explicit_model(spec: dict[str, object], *, carrier: str = "integer_plane", eta: int = 1,
                   rule: str = "quadratic") -> dict[str, object]:
    changed = copy.deepcopy(spec)
    changed["model"] = {"id": "supplied", "family": "amplitude_algebra", "carrier": carrier,
                        "product_square": -1 if carrier == "integer_plane" else 0,
                        "imaginary_weight": eta, "weight_rule": rule}
    return changed


def oracle(spec: dict[str, object], eta: int = 1) -> list[dict[str, object]]:
    # Deliberately independent of the production model and matrix helpers.
    preparation, alice, bob = spec["preparation"], spec["alice"], spec["bob"]
    assert isinstance(preparation, list) and isinstance(alice, list) and isinstance(bob, list)
    expected: list[dict[str, object]] = []
    for x in range(2):
        for y in range(2):
            table = []
            for i in range(2):
                line = []
                for j in range(2):
                    line.append([sum(alice[x][i][k] * preparation[k][l][coordinate] * bob[y][j][l]
                                     for k in range(2) for l in range(2)) for coordinate in range(2)])
                table.append(line)
            weights = [[a*a + eta*b*b for a, b in line] for line in table]
            total = sum(sum(line) for line in weights)
            probabilities = [[Fraction(w, total) for w in line] for line in weights]
            correlation = probabilities[0][0] - probabilities[0][1] - probabilities[1][0] + probabilities[1][1]
            win = sum((probabilities[i][j] for i in range(2) for j in range(2) if (i ^ j) == x*y), Fraction())
            expected.append({"x": x, "y": y, "state": table, "raw_total": str(total),
                "raw_weights": [[str(w) for w in line] for line in weights],
                "probabilities": [[str(p) for p in line] for line in probabilities],
                "alice_marginal": [str(sum(line, Fraction())) for line in probabilities],
                "bob_marginal": [str(sum((probabilities[i][j] for i in range(2)), Fraction())) for j in range(2)],
                "correlation": str(correlation), "game_win": str(win)})
    return expected


class NativeBellBridgeTests(unittest.TestCase):
    def test_exact_eight_controls_and_finite_completion_meaning(self) -> None:
        expected = {
            "native_bell_scalar_witness": SUCCESS, "native_bell_gaussian_witness": SUCCESS,
            "native_bell_scalar_identity": SUCCESS, "native_bell_gaussian_identity": SUCCESS,
            "native_bell_gaussian_scaled_preparation": SUCCESS,
            "native_bell_gaussian_zero": "inconclusive",
            "native_bell_gaussian_bad_operation": "unsupported",
            "native_bell_unknown_context_source": "unsupported",
        }
        self.assertEqual(set(fixtures()), set(expected))
        for name, status in expected.items():
            with self.subTest(name=name):
                result = report_for(name)
                self.assertEqual(result["status"], status)
                self.assertEqual(result["proof_status"], "not_attempted")
                self.assertEqual(result["empirical_status"], "not_tested")
                self.assertEqual(scope(result)["candidate_verdict"], "unchanged")
                self.assertEqual(scope(result)["proof_check"], "not_run_by_this_evaluator")
                check = rows(result["checks"])[0]
                self.assertEqual(check["id"], "native_bell_execution_completion_only")
                self.assertEqual((check["checked"], check["planned"]), (4 if status == SUCCESS else 0, 4))

    def test_witness_exact_oracle_marginals_chsh_and_game_win(self) -> None:
        literal = [
            [[[2, 0], [-1, 0]], [[1, 0], [2, 0]]],
            [[[2, 0], [1, 0]], [[-1, 0], [2, 0]]],
            [[[3, 0], [1, 0]], [[1, 0], [-3, 0]]],
            [[[1, 0], [3, 0]], [[3, 0], [-1, 0]]],
        ]
        for name in ("native_bell_scalar_witness", "native_bell_gaussian_witness"):
            spec = fixtures()[name]
            details = scope(report_for(spec=spec))
            contexts = rows(details["contexts"])
            self.assertEqual(contexts, oracle(spec))
            self.assertEqual([item["state"] for item in contexts], literal)
            self.assertEqual([item["raw_total"] for item in contexts], ["10", "10", "20", "20"])
            self.assertEqual([item["correlation"] for item in contexts], ["3/5", "3/5", "4/5", "-4/5"])
            self.assertEqual(details["chsh"], "14/5")
            self.assertEqual(details["uniform_setting_game_win"], "17/20")
            diagnostic = object_fields(details["no_signalling_diagnostic"])
            self.assertTrue(diagnostic["holds"])
            self.assertEqual(diagnostic["alice_marginal_differences_y0_minus_y1"], [["0", "0"], ["0", "0"]])
            self.assertEqual(diagnostic["bob_marginal_differences_x0_minus_x1"], [["0", "0"], ["0", "0"]])
            self.assertTrue(all(item[party] == ["1/2", "1/2"] for item in contexts
                                for party in ("alice_marginal", "bob_marginal")))
            source = object_fields(spec["model"])
            self.assertEqual(details["model_origin"], "exact_archived_source_specification_binding")
            self.assertEqual(details["source_specification_sha256"], pipeline.digest(source))
            self.assertEqual(details["source_missing_bridges"], source["missing_bridges"])

    def test_identity_protocol_is_not_rejected_or_ranked(self) -> None:
        for name in ("native_bell_scalar_identity", "native_bell_gaussian_identity"):
            result = report_for(name)
            self.assertEqual(result["status"], SUCCESS)
            self.assertEqual(scope(result)["chsh"], "2")
            self.assertEqual(scope(result)["uniform_setting_game_win"], "3/4")
            self.assertTrue(object_fields(scope(result)["no_signalling_diagnostic"])["holds"])
            self.assertEqual(result["rejection_scope"], "no_primitive_rejection_execution_diagnostics_only")

    def test_native_nonreal_preparation_uses_independent_integer_oracle(self) -> None:
        spec = explicit_model(fixtures()["native_bell_gaussian_witness"])
        spec["preparation"] = [[[1, 1], [-1, 2]], [[0, -1], [2, 1]]]
        details = scope(report_for(spec=spec))
        self.assertEqual(details["contexts"], oracle(spec))
        self.assertTrue(object_fields(details["no_signalling_diagnostic"])["holds"])

    def test_all_state_arithmetic_dispatches_to_bound_native_methods(self) -> None:
        with (
            patch.object(AmplitudeAlgebra, "add", autospec=True, side_effect=AmplitudeAlgebra.add) as add,
            patch.object(AmplitudeAlgebra, "multiply", autospec=True, side_effect=AmplitudeAlgebra.multiply) as multiply,
            patch.object(AmplitudeAlgebra, "weight", autospec=True, side_effect=AmplitudeAlgebra.weight) as weight,
        ):
            details = scope(report_for())
        self.assertEqual(details["chsh"], "14/5")
        self.assertGreaterEqual(add.call_count, 64)
        self.assertGreaterEqual(multiply.call_count, 128)
        self.assertGreaterEqual(weight.call_count, 20)

    def test_common_scaling_changes_raw_totals_not_direct_probabilities(self) -> None:
        spec = fixtures()["native_bell_gaussian_witness"]
        original = rows(scope(report_for(spec=spec))["contexts"])
        for field in ("preparation", "alice", "bob"):
            changed = copy.deepcopy(spec)
            values = changed[field]
            assert isinstance(values, list)
            changed[field] = [[[2*v for v in line] for line in matrix] for matrix in values]
            actual = rows(scope(report_for(spec=changed))["contexts"])
            for before, after in zip(original, actual, strict=True):
                self.assertEqual(after["probabilities"], before["probabilities"])
                self.assertEqual(Fraction(str(after["raw_total"])), 4 * Fraction(str(before["raw_total"])))
                self.assertEqual(after["correlation"], before["correlation"])

    def test_reference_continuation_breaks_global_scale_quotient(self) -> None:
        control = object_fields(scope(report_for())["common_scale_scope_countercontrol"])
        evaluations = rows(control["evaluations"])
        self.assertEqual([row["direct_probabilities"] for row in evaluations], [["1", "0"], ["1", "0"]])
        self.assertEqual([row["direct_raw_weights"] for row in evaluations], [["1", "0"], ["4", "0"]])
        self.assertEqual([row["fixed_reference_probabilities"] for row in evaluations],
                         [["1/2", "1/2"], ["4/5", "1/5"]])
        self.assertIn("homogeneous_continuations_not_global_quotient", str(control["conclusion"]))

    def test_scaled_norm_projective_inverse_and_integer_inverse_are_separate(self) -> None:
        operations = object_fields(scope(report_for())["operations"])
        a0, h = rows(operations["alice"])
        b0, b1 = rows(operations["bob"])
        self.assertTrue(a0["exact_norm_preserved"])
        self.assertTrue(a0["integer_inverse_exists"])
        for operation, scale, determinant in ((h, 2, -2), (b0, 5, 5), (b1, 5, 5)):
            self.assertTrue(operation["positive_scaled_isometry"])
            self.assertEqual(operation["weight_scale"], scale)
            self.assertFalse(operation["exact_norm_preserved"])
            self.assertFalse(operation["integer_inverse_exists"])
            self.assertFalse(operation["integer_lattice_bijection"])
            self.assertEqual(operation["integer_determinant"], determinant)
            self.assertEqual(operation["transpose_projective_inverse_scale"], scale)

    def test_zero_weight_never_divides_and_low_budget_does_no_readout(self) -> None:
        zero = report_for("native_bell_gaussian_zero")
        self.assertEqual(scope(zero)["execution_status"], "undefined_readout")
        self.assertNotIn("chsh", scope(zero))
        for budget in (1, 2, 3):
            with patch.object(AmplitudeAlgebra, "weight", side_effect=AssertionError("hidden readout")):
                result = report_for(budget=budget)
            self.assertEqual(result["status"], "inconclusive")
            self.assertEqual(scope(result)["contexts"], [])
        # A nonzero vector can also have zero weight in a permitted degenerate algebra.
        spec = explicit_model(fixtures()["native_bell_gaussian_witness"], eta=0)
        spec["preparation"] = [[[0, 1], [0, 0]], [[0, 0], [0, 0]]]
        self.assertEqual(scope(report_for(spec=spec))["execution_status"], "undefined_readout")

    def test_unsupported_bridge_source_weight_operation_and_carrier_preflight(self) -> None:
        base = fixtures()["native_bell_gaussian_witness"]
        unknown = copy.deepcopy(base)
        unknown["bridge"] = "unknown_v1"
        spoofed = copy.deepcopy(base)
        source = object_fields(spoofed["model"])
        source["declared_status"] = "changed without changing id"
        spoofed["model"] = source
        negative = explicit_model(base, eta=-1)
        quartic = explicit_model(base, rule="quartic")
        scalar = explicit_model(base, carrier="integer_scalar", eta=0)
        scalar["preparation"] = [[[1, 1], [0, 0]], [[0, 0], [1, 0]]]
        cases = [unknown, spoofed, negative, quartic, scalar,
                 fixtures()["native_bell_gaussian_bad_operation"], fixtures()["native_bell_unknown_context_source"]]
        for spec in cases:
            with self.subTest(id=spec["id"]), patch.object(AmplitudeAlgebra, "multiply", side_effect=AssertionError("ran")):
                result = report_for(spec=spec)
            self.assertEqual(result["status"], "unsupported")
            self.assertEqual(scope(result)["contexts"], [])
            self.assertNotIn("chsh", scope(result))

    def test_unknown_source_id_spoof_cannot_acquire_a_native_binding(self) -> None:
        spec = fixtures()["native_bell_unknown_context_source"]
        source = object_fields(spec["model"])
        source["id"] = "pair_history_gaussian_realization"
        spec["model"] = source
        result = report_for(spec=spec)
        self.assertEqual(result["status"], "unsupported")
        self.assertEqual(scope(result)["model_origin"], "unbound_source_snapshot")
        self.assertNotIn("source_specification_sha256", scope(result))
        parsed = parse_native_bell_bridge(fixtures()["native_bell_gaussian_witness"])
        self.assertEqual(parsed.specification(), fixtures()["native_bell_gaussian_witness"])

    def test_strict_bounded_schema_rejects_bools_extra_fields_and_nested_wrappers(self) -> None:
        base = fixtures()["native_bell_gaussian_witness"]
        malformed: list[dict[str, object]] = []
        for value in (True, False, 5, -5, 1.0, "1"):
            amplitude = copy.deepcopy(base)
            amplitude["preparation"] = [[[value, 0], [0, 0]], [[0, 0], [1, 0]]]
            malformed.append(amplitude)
            matrix = copy.deepcopy(base)
            matrix["alice"] = [[[value, 0], [0, 1]], [[1, 1], [1, -1]]]
            malformed.append(matrix)
        for field, malformed_value in (("extra", 1), ("alice", []), ("bob", [[[1, 0], [0, 1]]]),
                                       ("preparation", [[1, 0], [0, 1]]), ("model", base)):
            changed = copy.deepcopy(base)
            changed[field] = malformed_value
            malformed.append(changed)
        for spec in malformed:
            with self.subTest(spec=spec["id"]), self.assertRaises((ValueError, TypeError)):
                parse_native_bell_bridge(spec)

    def test_cache_hit_replay_integrity_and_source_change_guards(self) -> None:
        spec = fixtures()["native_bell_gaussian_witness"]
        with tempfile.TemporaryDirectory() as temporary:
            cache = Path(temporary)
            first = pipeline.run_batch([spec], Limits(max_cases=4), cache)[0]
            with patch.object(pipeline, "compute", side_effect=AssertionError("cache recomputed")):
                second = pipeline.run_batch([spec], Limits(max_cases=4), cache)[0]
            self.assertTrue(second.reused)
            self.assertEqual(second.report, first.report)
            assert first.artifact is not None
            self.assertEqual(pipeline.replay_artifact(first.artifact), first.report)
            sources = pipeline.provenance()
            changed = copy.deepcopy(sources)
            object_fields(changed["source_sha256"])
            changed["source_sha256"] = {"changed": "0" * 64}
            with patch.object(pipeline, "provenance", return_value=changed), self.assertRaisesRegex(ValueError, "sources changed since import"):
                pipeline.run_batch([spec], Limits(max_cases=4), cache)
            # Even cache-only batches recheck the sources after the full batch.
            with patch.object(pipeline, "provenance", side_effect=[sources, changed]), self.assertRaisesRegex(ValueError, "sources changed during batch"):
                pipeline.run_batch([spec], Limits(max_cases=4), cache)
            envelope = json.loads(first.artifact.read_text())
            envelope["report"]["scope"]["chsh"] = "4"
            first.artifact.write_text(json.dumps(envelope))
            with self.assertRaisesRegex(ValueError, "integrity/request mismatch"):
                pipeline.run_batch([spec], Limits(max_cases=4), cache)

    def test_existing_native_operation_and_universe_raw_weight_semantics_unchanged(self) -> None:
        model = {"id": "gaussian", "family": "amplitude_algebra", "carrier": "integer_plane",
                 "product_square": -1, "imaginary_weight": 1, "weight_rule": "quadratic"}
        previous = analyze_operation(model, {"id": "hadamard", "kind": "integer_matrix", "matrix": [[1, 1], [1, -1]]})
        self.assertFalse(object_fields(previous["weight_preservation"])["holds"])
        self.assertFalse(object_fields(previous["reversibility"])["holds"])
        self.assertFalse(object_fields(previous["supplied_contracts"])["closed_reversible_weight"])
        spec = {"id": "raw_scope_control", "family": "universe_bench", "scenario": "two_path_v1", "model": model,
                "preparations": [{"id": "aligned", "left": [1, 0], "right": [1, 0],
                                  "left_factor": [1, 0], "right_factor": [1, 0]}]}
        old = scope(pipeline.run_batch([spec], Limits(max_cases=9))[0].report)
        self.assertEqual(rows(old["completed_preparations"])[0]["raw_weights"],
                         {"both": "4", "left_only": "1", "right_only": "1"})
        self.assertIn("not_probability", str(old["weight_meaning"]))


if __name__ == "__main__":
    unittest.main()
