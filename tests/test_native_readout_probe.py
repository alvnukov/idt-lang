"""Independent exact response oracles; finite diagnostics are not physical verdicts."""

from __future__ import annotations

import copy
import tempfile
import unittest
from fractions import Fraction
from pathlib import Path
from unittest.mock import patch

from theory_experiments import candidate_pipeline as pipeline
from theory_experiments.amplitude_algebra import AmplitudeAlgebra
from theory_experiments.candidate_history import History, record_batch
from theory_experiments.native_bell_bridge import (
    evaluate_native_bell_bridge,
    parse_native_bell_bridge,
)
from theory_experiments.native_readout_probe import parse_native_readout_probe
from theory_experiments.primitive_screen import Limits, load_json, object_fields

ROOT = Path(__file__).resolve().parents[1]
SUCCESS = "no_counterexample_within_bounds"


def fixtures() -> dict[str, dict[str, object]]:
    raw = load_json(ROOT / "data/native_readout_controls.json")
    assert isinstance(raw, list)
    return {str(object_fields(value)["id"]): object_fields(value) for value in raw}


def report_for(name: str = "readout_scalar_bell_native", *, spec: dict[str, object] | None = None,
               budget: int = 4) -> dict[str, object]:
    return pipeline.run_batch([fixtures()[name] if spec is None else spec], Limits(max_cases=budget))[0].report


def scope(report: dict[str, object]) -> dict[str, object]:
    return object_fields(report["scope"])


def contexts(report: dict[str, object]) -> list[dict[str, object]]:
    values = scope(report)["response_contexts"]
    assert isinstance(values, list)
    return [object_fields(value) for value in values]


def oracle(spec: dict[str, object]) -> list[dict[str, object]]:
    # Independent matrix arithmetic and response definitions, not production trace/probabilities.
    protocol = object_fields(spec["protocol"])
    preparation, alice, bob = protocol["preparation"], protocol["alice"], protocol["bob"]
    assert isinstance(preparation, list) and isinstance(alice, list) and isinstance(bob, list)
    model = object_fields(protocol["model"])
    eta = model["imaginary_weight"] if model["family"] == "amplitude_algebra" else 1
    assert isinstance(eta, int)
    expected: list[dict[str, object]] = []
    for x in range(2):
        for y in range(2):
            raw = []
            for i in range(2):
                row = []
                for j in range(2):
                    a, b = (sum(alice[x][i][k] * preparation[k][l][coordinate] * bob[y][j][l]
                                for k in range(2) for l in range(2)) for coordinate in range(2))
                    row.append(a*a + eta*b*b)
                raw.append(row)
            if spec["response"] == "native_weight":
                weights = raw
            elif spec["response"] == "squared_native_weight":
                weights = [[value**2 for value in row] for row in raw]
            else:
                assert spec["response"] == "spike_49"
                weights = [[value + int(value == 49) for value in row] for row in raw]
            total = sum(sum(row) for row in weights)
            probabilities = [[Fraction(value, total) for value in row] for row in weights]
            expected.append({"x": x, "y": y,
                "native_raw_weights": [[str(value) for value in row] for row in raw],
                "response_weights": [[str(value) for value in row] for row in weights],
                "response_total": str(total),
                "probabilities": [[str(value) for value in row] for row in probabilities],
                "alice_marginal": [str(sum(row, Fraction())) for row in probabilities],
                "bob_marginal": [str(probabilities[0][j] + probabilities[1][j]) for j in range(2)],
                "correlation": str(probabilities[0][0] - probabilities[0][1] - probabilities[1][0] + probabilities[1][1]),
                "game_win": str(sum((probabilities[i][j] for i in range(2) for j in range(2)
                                     if (i ^ j) == x*y), Fraction()))})
    return expected


class NativeReadoutProbeTests(unittest.TestCase):
    def test_twelve_controls_exact_status_and_claim_boundaries(self) -> None:
        values = fixtures()
        self.assertEqual(len(values), 12)
        self.assertLessEqual(len((ROOT / "data/native_readout_controls.json").read_bytes()), 131072)
        complete = 0
        for name in values:
            with self.subTest(name=name):
                report = report_for(name)
                expected = "inconclusive" if name == "readout_zero" else (
                    "unsupported" if name == "readout_unbound_source" else SUCCESS)
                self.assertEqual(report["status"], expected)
                complete += report["status"] == SUCCESS
                self.assertEqual(report["proof_status"], "not_attempted")
                self.assertEqual(report["empirical_status"], "not_tested")
                details = scope(report)
                self.assertEqual(details["candidate_verdict"], "unchanged")
                self.assertEqual(details["scientific_status"], "unassessed")
                self.assertEqual(details["proof_check"], "not_run_by_this_evaluator")
                self.assertIn("unchanged", str(details["original_native_weight_semantics"]))
                self.assertIn("separate_reference", str(details["native_protocol_evidence_readout"]))
                self.assertEqual(report["rejection_scope"], "no_primitive_rejection_execution_diagnostics_only")
                self.assertTrue(details["missing_bridges"])
        self.assertEqual(complete, 10)

    def test_all_complete_controls_match_independent_oracle(self) -> None:
        for name, spec in fixtures().items():
            if name not in ("readout_zero", "readout_unbound_source"):
                with self.subTest(name=name):
                    self.assertEqual(contexts(report_for(name)), oracle(spec))

    def test_same_symmetric_bell_trace_has_different_chsh_but_equal_marginals(self) -> None:
        for prefix in ("readout_scalar_bell", "readout_gaussian_bell"):
            for suffix, chsh, win in (("native", "14/5", "17/20"),
                                      ("squared", "2590/697", "2689/2788")):
                report = report_for(prefix + "_" + suffix)
                self.assertEqual(scope(report)["chsh"], chsh)
                self.assertEqual(scope(report)["uniform_setting_game_win"], win)
                self.assertTrue(object_fields(scope(report)["no_signalling_diagnostic"])["holds"])
                self.assertTrue(all(row[party] == ["1/2", "1/2"] for row in contexts(report)
                                    for party in ("alice_marginal", "bob_marginal")))

    def test_nonsymmetric_preparation_detects_fourth_response_not_spike(self) -> None:
        native = report_for("readout_nonsymmetric_native")
        squared = report_for("readout_nonsymmetric_squared")
        spike = report_for("readout_nonsymmetric_spike")
        self.assertEqual([row["alice_marginal"] for row in contexts(native)][:2],
                         [["1/3", "2/3"], ["1/3", "2/3"]])
        self.assertEqual([row["alice_marginal"] for row in contexts(squared)][:2],
                         [["1/3", "2/3"], ["1/9", "8/9"]])
        self.assertFalse(object_fields(scope(squared)["no_signalling_diagnostic"])["holds"])
        self.assertEqual(squared["status"], SUCCESS)  # Completion despite conditional incompatibility.
        self.assertEqual(contexts(spike), contexts(native))

    def test_spike49_evades_benchmark_but_reference_control_finds_it(self) -> None:
        self.assertEqual(contexts(report_for("readout_scalar_bell_spike")), contexts(report_for()))
        native = contexts(report_for("readout_reference_3_4_native"))
        spike_report = report_for("readout_reference_3_4_spike")
        spike = contexts(spike_report)
        self.assertEqual([row["alice_marginal"] for row in native][:2],
                         [["25/26", "1/26"], ["25/26", "1/26"]])
        self.assertEqual([row["alice_marginal"] for row in spike][:2],
                         [["25/26", "1/26"], ["51/53", "2/53"]])
        self.assertFalse(object_fields(scope(spike_report)["no_signalling_diagnostic"])["holds"])
        self.assertIn("not_primitive_rejection", str(object_fields(scope(spike_report)["no_signalling_diagnostic"])["meaning"]))

    def test_protocol_hash_and_reference_readout_exclude_selected_response(self) -> None:
        reports = [scope(report_for("readout_scalar_bell_" + suffix)) for suffix in ("native", "squared", "spike")]
        self.assertEqual(len({str(report["protocol_sha256"]) for report in reports}), 1)
        self.assertTrue(all(report["native_protocol_evidence"] == reports[0]["native_protocol_evidence"] for report in reports))
        protocol = object_fields(fixtures()["readout_scalar_bell_native"]["protocol"])
        self.assertEqual(reports[0]["protocol_sha256"], pipeline.digest(protocol))
        native = object_fields(reports[0]["native_protocol_evidence"])
        self.assertEqual(native["source_specification_sha256"], pipeline.digest(protocol["model"]))
        self.assertEqual(native["model_origin"], "exact_archived_source_specification_binding")

    def test_native_methods_dispatch_and_original_native_semantics(self) -> None:
        with (
            patch.object(AmplitudeAlgebra, "add", autospec=True, side_effect=AmplitudeAlgebra.add) as add,
            patch.object(AmplitudeAlgebra, "multiply", autospec=True, side_effect=AmplitudeAlgebra.multiply) as multiply,
            patch.object(AmplitudeAlgebra, "weight", autospec=True, side_effect=AmplitudeAlgebra.weight) as weight,
        ):
            report = report_for("readout_scalar_bell_squared")
        self.assertGreaterEqual(add.call_count, 64)
        self.assertGreaterEqual(multiply.call_count, 128)
        self.assertGreaterEqual(weight.call_count, 20)
        protocol = parse_native_bell_bridge(fixtures()["readout_scalar_bell_squared"]["protocol"])
        _, direct = evaluate_native_bell_bridge(protocol, Limits(max_cases=4))
        self.assertEqual(scope(report)["native_protocol_evidence"], direct)
        self.assertEqual(direct["chsh"], "14/5")
        self.assertEqual(scope(report)["chsh"], "2590/697")

    def test_selected_readout_consumes_raw_weights_not_reference_probabilities(self) -> None:
        spec = fixtures()["readout_scalar_bell_squared"]
        protocol = parse_native_bell_bridge(spec["protocol"])
        checks, trace = evaluate_native_bell_bridge(protocol, Limits(max_cases=4))
        rows = trace["contexts"]
        assert isinstance(rows, list)
        for row in rows:
            row["probabilities"] = [["0", "0"], ["0", "0"]]
            row["raw_weights"] = [["1", "2"], ["3", "4"]]
        with patch("theory_experiments.native_readout_probe.evaluate_native_bell_bridge", return_value=(checks, trace)):
            report = report_for(spec=spec)
        for row in contexts(report):
            self.assertEqual(row["response_weights"], [["1", "4"], ["9", "16"]])
            self.assertEqual(row["probabilities"], [["1/30", "2/15"], ["3/10", "8/15"]])

    def test_nonreal_gaussian_trace_is_executed_not_scalar_special_cased(self) -> None:
        spec = fixtures()["readout_gaussian_bell_squared"]
        protocol = object_fields(spec["protocol"])
        protocol["preparation"] = [[[1, 1], [-1, 2]], [[0, -1], [2, 1]]]
        spec["protocol"] = protocol
        self.assertEqual(contexts(report_for(spec=spec)), oracle(spec))

    def test_atomic_budget_zero_and_unknown_response_preflight(self) -> None:
        for budget in (1, 2, 3):
            with patch.object(AmplitudeAlgebra, "weight", side_effect=AssertionError("hidden readout")):
                report = report_for(budget=budget)
            self.assertEqual(report["status"], "inconclusive")
            self.assertEqual(contexts(report), [])
            self.assertEqual(object_fields(scope(report)["native_protocol_evidence"])["contexts"], [])
        self.assertEqual(report_for("readout_zero")["status"], "inconclusive")
        unknown = fixtures()["readout_scalar_bell_native"]
        unknown["response"] = "future_response"
        with patch("theory_experiments.native_readout_probe.evaluate_native_bell_bridge", side_effect=AssertionError("ran")):
            report = report_for(spec=unknown)
        self.assertEqual(report["status"], "unsupported")
        self.assertEqual(contexts(report), [])

    def test_binding_forgery_unknown_bridge_and_inadmissible_operation_are_unsupported(self) -> None:
        for mutation in ("source", "bridge", "operation"):
            spec = fixtures()["readout_scalar_bell_native"]
            protocol = object_fields(spec["protocol"])
            if mutation == "source":
                source = object_fields(protocol["model"])
                source["declared_status"] = "forged same id"
                protocol["model"] = source
            elif mutation == "bridge":
                protocol["bridge"] = "unknown_bridge"
            else:
                protocol["alice"] = [[[1, 0], [0, 1]], [[1, 0], [0, 2]]]
            spec["protocol"] = protocol
            with patch.object(AmplitudeAlgebra, "multiply", side_effect=AssertionError("ran")):
                report = report_for(spec=spec)
            self.assertEqual(report["status"], "unsupported")
            self.assertEqual(contexts(report), [])

    def test_strict_schema_nested_protocol_and_existing_integer_bounds(self) -> None:
        base = fixtures()["readout_scalar_bell_native"]
        for field, value in (("extra", 1), ("response", True), ("response", {"power": 2}),
                             ("protocol", base), ("family", "not_readout")):
            malformed = copy.deepcopy(base)
            malformed[field] = value
            with self.subTest(field=field), self.assertRaises((ValueError, TypeError)):
                parse_native_readout_probe(malformed)
        for amplitude_value in (True, False, 5, -5, "1", 1.0):
            malformed = copy.deepcopy(base)
            protocol = object_fields(malformed["protocol"])
            protocol["preparation"] = [[[amplitude_value, 0], [0, 0]], [[0, 0], [1, 0]]]
            malformed["protocol"] = protocol
            with self.subTest(value=amplitude_value), self.assertRaises((ValueError, TypeError)):
                parse_native_readout_probe(malformed)
        self.assertEqual(parse_native_readout_probe(base).specification(), base)

    def test_cache_replay_and_temporary_history_integration(self) -> None:
        spec = fixtures()["readout_scalar_bell_native"]
        with tempfile.TemporaryDirectory() as temporary:
            cache = Path(temporary) / "cache"
            first = pipeline.run_batch([spec], Limits(max_cases=4), cache)[0]
            second = pipeline.run_batch([spec], Limits(max_cases=4), cache)[0]
            self.assertTrue(second.reused)
            self.assertEqual(first.report, second.report)
            assert first.artifact is not None
            self.assertEqual(pipeline.replay_artifact(first.artifact), first.report)
            history = History(Path(temporary) / "history")
            recorded = record_batch([spec], Limits(max_cases=4), history=history)
            self.assertIsNotNone(recorded)
        self.assertIn("theory_experiments/native_readout_probe.py", pipeline.SOURCE_PATHS)
        self.assertIn("Proofs/QMClosure/NativeReadoutSelection.lean", pipeline.SOURCE_PATHS)


if __name__ == "__main__":
    unittest.main()
