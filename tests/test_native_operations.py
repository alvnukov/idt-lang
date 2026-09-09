"""Operation contracts must not become unconditional candidate rejection criteria."""

from __future__ import annotations

import contextlib
import io
import itertools
import tempfile
import unittest
from pathlib import Path
from unittest.mock import patch

from scripts import check_native_observability as cli
from theory_experiments.amplitude_algebra import AmplitudeAlgebra
from theory_experiments.native_operations import (
    IntegerMatrix,
    analyze_operation,
    parse_operation,
)
from theory_experiments.primitive_screen import canonical_json, load_json, object_fields

ROOT = Path(__file__).resolve().parents[1]


def matrix(p: int, q: int, r: int, s: int) -> dict[str, object]:
    return {"id": "matrix", "kind": "integer_matrix", "matrix": [[p, q], [r, s]]}


def holds(report: dict[str, object], property_name: str) -> object:
    return object_fields(report[property_name])["holds"]


def saved_inputs() -> tuple[list[object], list[object]]:
    specs = object_fields(load_json(ROOT / "data/native_observability_review.json"))["candidates"]
    operations = load_json(ROOT / "data/native_operation_probes.json")
    assert isinstance(specs, list) and isinstance(operations, list)
    return specs, operations


class NativeOperationTests(unittest.TestCase):
    def test_saved_review_replays_every_pair_without_refreshing_the_snapshot(self) -> None:
        specs, operations = saved_inputs()
        saved = object_fields(load_json(ROOT / "data/native_operation_review.json"))
        self.assertEqual(saved["candidates"], specs)
        self.assertEqual(saved["operations"], operations)
        self.assertEqual(saved["reports"], [analyze_operation(spec, op)
                                         for spec in specs for op in operations])
        self.assertEqual(saved["schema"], "idt-native-operation-audit/1")

    def test_all_retained_operation_candidate_pairs_match_reviewed_contract_table(self) -> None:
        specs, operations = saved_inputs()
        # Columns: identity, hidden shear, parity, swap, quarter-turn, scale, projection.
        # Each entry: closed+reversible+W / additivity-enhanced contract; X = outside carrier.
        expected = [
            ["TT", "X", "TT", "X", "X", "FF", "TT"],
            ["TT", "FF", "TF", "TT", "TT", "FF", "FF"],
            ["TT", "TT", "TF", "FF", "FF", "FF", "FF"],
            ["TT", "TT", "TF", "FF", "FF", "FF", "FF"],
            ["TT", "FF", "TF", "FF", "FF", "FF", "FF"],
        ]
        self.assertEqual([object_fields(op)["id"] for op in operations], [
            "identity", "hidden_shear", "parity_sign", "coordinate_swap", "quarter_turn",
            "scale_two", "scalar_projection"])
        self.assertEqual(len(specs), len(expected))
        for spec, row in zip(specs, expected, strict=True):
            for op, flags in zip(operations, row, strict=True):
                report = analyze_operation(spec, op)
                self.assertEqual(report["candidate_verdict"], "unchanged")
                self.assertEqual(report["physical_admissibility"], "unassessed")
                self.assertEqual(report["empirical_status"], "not_tested")
                self.assertEqual(report["proof_status"], "not_checked_by_this_command")
                if flags == "X":
                    self.assertEqual(report["status"], "outside_carrier")
                    self.assertNotIn("supplied_contracts", report)
                else:
                    self.assertEqual(report["status"], "analyzed")
                    contracts = object_fields(report["supplied_contracts"])
                    self.assertEqual(contracts["closed_reversible_weight"], flags[0] == "T")
                    self.assertEqual(contracts["coherent_reversible_weight"], flags[1] == "T")
                    self.assertFalse(contracts["multiplicativity_is_required"])

    def test_parity_preserves_all_individual_weights_but_reveals_dual_coordinate(self) -> None:
        operation = {"id": "parity", "kind": "parity_sign"}
        for eta in range(-2, 3):
            model = AmplitudeAlgebra("parity_check", "integer_plane", 0, eta)
            transformation = parse_operation(operation)
            for point in model.grid(3):
                self.assertEqual(transformation.apply(transformation.apply(point)), point)
                self.assertEqual(model.weight(transformation.apply(point)), model.weight(point))
            report = analyze_operation(model.specification(), operation)
            self.assertTrue(holds(report, "weight_preservation"))
            self.assertFalse(holds(report, "additivity"))
            self.assertFalse(holds(report, "pair_sum_weight"))
            witness = object_fields(report["coherent_witness"])
            self.assertEqual(witness["initial_weight"], 4 + eta)
            self.assertEqual(witness["transformed_weight"], eta)
            self.assertFalse(holds(report, "multiplicativity_diagnostic_only"))
            if eta == 0:
                quotient = object_fields(report["old_quotient_stability"])
                self.assertFalse(quotient["holds"])
                self.assertEqual(object_fields(quotient["witness"])["output_weights"], [4, 0])

    def test_exact_matrix_coefficients_match_independent_native_evaluation(self) -> None:
        for eta in range(-2, 3):
            model = AmplitudeAlgebra("matrix_check", "integer_plane", -1, eta)
            for p, q, r, s in itertools.product(range(-1, 2), repeat=4):
                op = matrix(p, q, r, s)
                transform = IntegerMatrix("matrix", p, q, r, s)
                report = analyze_operation(model.specification(), op)
                coeff = object_fields(object_fields(report["weight_preservation"])["defect_coefficients"])
                a2, ab, b2 = coeff["a2"], coeff["ab"], coeff["b2"]
                assert isinstance(a2, int) and isinstance(ab, int) and isinstance(b2, int)
                for a, b in model.grid(2):
                    self.assertEqual(model.weight(transform.apply((a, b))) - model.weight((a, b)),
                                     a2 * a * a + ab * a * b + b2 * b * b)
                # Independent small grid tests the analytic classifier; not used to claim universality.
                sample_preserved = all(model.weight(transform.apply(x)) == model.weight(x)
                                       for x in model.grid(1))
                self.assertEqual(holds(report, "weight_preservation"), sample_preserved)

    def test_basis_multiplicativity_check_matches_native_pairs(self) -> None:
        for k in range(-2, 3):
            model = AmplitudeAlgebra("product_check", "integer_plane", k, 1)
            for p, q, r, s in itertools.product(range(-1, 2), repeat=4):
                transform = IntegerMatrix("matrix", p, q, r, s)
                actual = all(transform.apply(model.multiply(x, y)) ==
                             model.multiply(transform.apply(x), transform.apply(y))
                             for x, y in itertools.product(model.grid(1), repeat=2))
                report = analyze_operation(model.specification(), matrix(p, q, r, s))
                self.assertEqual(holds(report, "multiplicativity_diagnostic_only"), actual)

    def test_quarter_turn_is_good_coherent_control_but_not_multiplicative(self) -> None:
        gaussian = AmplitudeAlgebra("gaussian", "integer_plane", -1, 1)
        report = analyze_operation(gaussian.specification(), matrix(0, -1, 1, 0))
        self.assertTrue(object_fields(report["supplied_contracts"])["coherent_reversible_weight"])
        self.assertFalse(holds(report, "multiplicativity_diagnostic_only"))
        self.assertIsNone(holds(report, "old_quotient_stability"))
        transform = IntegerMatrix("quarter", 0, -1, 1, 0)
        for point in gaussian.grid(2):
            self.assertEqual(transform.apply(point), gaussian.multiply((0, 1), point))

    def test_actual_scalar_carrier_not_ambient_plane_controls_reversibility(self) -> None:
        scalar = AmplitudeAlgebra("scalar", "integer_scalar", 0, 0)
        for q, s in itertools.product(range(-2, 3), repeat=2):
            report = analyze_operation(scalar.specification(), matrix(1, q, 0, s))
            self.assertTrue(holds(report, "reversibility"))
            self.assertTrue(holds(report, "weight_preservation"))
            self.assertTrue(holds(report, "old_quotient_stability"))
        report = analyze_operation(scalar.specification(), matrix(1, 0, 1, 1))
        self.assertFalse(report["carrier_closed"])
        self.assertEqual(report["status"], "outside_carrier")

    def test_dual_quotient_does_not_require_reversibility(self) -> None:
        dual = AmplitudeAlgebra("dual", "integer_plane", 0, 0)
        projection = analyze_operation(dual.specification(), matrix(1, 0, 0, 0))
        self.assertTrue(holds(projection, "old_quotient_stability"))
        self.assertFalse(holds(projection, "reversibility"))
        swap = analyze_operation(dual.specification(), matrix(0, 1, 1, 0))
        self.assertFalse(holds(swap, "old_quotient_stability"))

    def test_source_binding_cannot_be_forged_and_nonquadratic_is_unsupported(self) -> None:
        specs, operations = saved_inputs()
        source = object_fields(specs[0])
        report = analyze_operation({**source, "declared_status": "modified"}, operations[0])
        self.assertEqual(report["status"], "unsupported")
        self.assertEqual(report["missing_bridges"], source["missing_bridges"])
        model = AmplitudeAlgebra("quartic", "integer_scalar", 0, 0, "quartic")
        self.assertEqual(analyze_operation(model.specification(), operations[0])["status"], "unsupported")

    def test_operation_parser_rejects_unsafe_or_malformed_inputs(self) -> None:
        for invalid in [None, {"id": "op", "kind": "python", "matrix": [[1, 0], [0, 1]]},
                        {**matrix(1, 0, 0, 1), "extra": 1},
                        {"id": "op", "kind": "integer_matrix", "matrix": [[True, 0], [0, 1]]},
                        {"id": "op", "kind": "integer_matrix", "matrix": [[1, 0, 0]]},
                        matrix(5, 0, 0, 1)]:
            with self.assertRaises((ValueError, TypeError)):
                parse_operation(invalid)

    def test_cli_preserves_history_and_never_returns_candidate_rejection(self) -> None:
        history = ROOT / "data/candidate_history"
        before = {str(p.relative_to(history)): p.read_bytes() for p in history.rglob("*") if p.is_file()}
        with contextlib.redirect_stdout(io.StringIO()) as output:
            code = cli.main(["--batch-file", str(ROOT / "data/native_observability_probes.json"),
                             "--operations-file", str(ROOT / "data/native_operation_probes.json")])
        self.assertEqual(code, 0)
        self.assertIn('"idt-native-operation-audit/1"', output.getvalue())
        after = {str(p.relative_to(history)): p.read_bytes() for p in history.rglob("*") if p.is_file()}
        self.assertEqual(before, after)

    def test_operation_limits_and_loaded_source_binding(self) -> None:
        specs, operations = saved_inputs()
        with patch.object(cli, "LOADED_OPERATION_SHA256", "old"), self.assertRaisesRegex(ValueError, "since import"):
            cli.evidence(specs, operations)
        for candidates, ops in [(specs, []), (specs, operations * 3), (specs * 8, operations)]:
            with self.assertRaises(ValueError):
                cli.evidence(candidates, ops)
        with tempfile.TemporaryDirectory() as directory:
            operation_file = Path(directory) / "invalid.json"
            operation_file.write_text(canonical_json(None))
            with contextlib.redirect_stderr(io.StringIO()), contextlib.redirect_stdout(io.StringIO()):
                self.assertEqual(cli.main([
                    "--batch-file", str(ROOT / "data/native_observability_probes.json"),
                    "--operations-file", str(operation_file)]), 2)


if __name__ == "__main__":
    unittest.main()
