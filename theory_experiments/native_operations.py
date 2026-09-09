"""Exact supplied-operation diagnostics; never a physical candidate rejection gate."""

from __future__ import annotations

import hashlib
import itertools
from dataclasses import dataclass
from pathlib import Path

from theory_experiments.amplitude_algebra import (
    Amplitude,
    AmplitudeAlgebra,
    parse_amplitude_algebra,
)
from theory_experiments.candidate_pipeline import digest
from theory_experiments.native_observability import analyze_projection
from theory_experiments.primitive_screen import bounded_int, candidate_id, object_fields

LOADED_MODULE_SHA256 = hashlib.sha256(Path(__file__).read_bytes()).hexdigest()


@dataclass(frozen=True)
class IntegerMatrix:
    id: str
    p: int
    q: int
    r: int
    s: int

    def __post_init__(self) -> None:
        candidate_id(self.id)
        for entry in (self.p, self.q, self.r, self.s):
            bounded_int(entry, -4, 4)

    def apply(self, value: Amplitude) -> Amplitude:
        a, b = value
        return self.p * a + self.q * b, self.r * a + self.s * b


@dataclass(frozen=True)
class ParitySign:
    id: str

    def __post_init__(self) -> None:
        candidate_id(self.id)

    def apply(self, value: Amplitude) -> Amplitude:
        a, b = value
        return (a if b % 2 == 0 else -a), b


def parse_operation(value: object) -> IntegerMatrix | ParitySign:
    row = object_fields(value)
    if row.get("kind") == "parity_sign":
        object_fields(row, {"id", "kind"})
        return ParitySign(candidate_id(row["id"]))
    object_fields(row, {"id", "kind", "matrix"})
    if row["kind"] != "integer_matrix":
        raise ValueError("unsupported operation kind; no executable input is accepted")
    matrix = row["matrix"]
    if not isinstance(matrix, list) or len(matrix) != 2:
        raise ValueError("operation matrix must have two rows")
    entries: list[int] = []
    for cells in matrix:
        if not isinstance(cells, list) or len(cells) != 2:
            raise ValueError("operation matrix must have two columns")
        entries.extend(bounded_int(cell, -4, 4) for cell in cells)
    return IntegerMatrix(candidate_id(row["id"]), *entries)


def _multiplicativity(model: AmplitudeAlgebra,
                     operation: IntegerMatrix | ParitySign) -> dict[str, object]:
    # For a linear map both sides are bilinear: basis pairs exhaust the coefficients.
    # This reduction is NOT applied to nonlinear operations.
    if isinstance(operation, IntegerMatrix):
        basis = ((1, 0),) if model.carrier == "integer_scalar" else ((1, 0), (0, 1))
        pairs = tuple(itertools.product(basis, repeat=2))
        reason = "bilinear_identity_checked_on_carrier_basis_pairs"
    elif model.carrier == "integer_scalar":
        return {"holds": True, "reason": "parity_is_identity_on_scalar_carrier"}
    else:
        pairs = (((2, 0), (1, 1)),)
        reason = "explicit_nonlinear_counterexample"
    defects: list[object] = []
    for left, right in pairs:
        actual = operation.apply(model.multiply(left, right))
        expected = model.multiply(operation.apply(left), operation.apply(right))
        defects.append({"left": list(left), "right": list(right),
                        "map_of_product": list(actual), "product_of_maps": list(expected)})
    holds = all(object_fields(row)["map_of_product"] == object_fields(row)["product_of_maps"]
                for row in defects)
    return {"holds": holds, "reason": reason, "evaluations": defects}


def _quotient(model: AmplitudeAlgebra, operation: IntegerMatrix | ParitySign,
              projection: dict[str, object]) -> dict[str, object]:
    if projection["status"] != "preserves_declared_grammar":
        return {"holds": None, "reason": "scalar_projection_was_not_a_valid_quotient"}
    if model.carrier == "integer_scalar":
        return {"holds": True, "reason": "identity_quotient_on_scalar_carrier"}
    if isinstance(operation, IntegerMatrix) and operation.q == 0:
        return {"holds": True, "reason": "output_real_depends_only_on_input_real"}
    if isinstance(operation, IntegerMatrix):
        left, right, reference = (0, 0), (0, 1), (0, 0)
    else:
        left, right, reference = (1, 0), (1, 1), (1, 0)
    weights = [model.weight(model.add(operation.apply(x), reference)) for x in (left, right)]
    assert left[0] == right[0] and weights[0] != weights[1]
    return {"holds": False, "reason": "added_operation_invalidates_old_quotient_not_candidate",
            "witness": {"left": list(left), "right": list(right),
                        "fixed_reference": list(reference), "output_weights": weights}}


def analyze_operation(candidate_spec: object, operation_spec: object) -> dict[str, object]:
    """Analyze two reviewed formula families on the actual supplied integer carrier.

    Contract flags are exact algebraic diagnostics, not claims that any operation,
    coherent reference, or preparation is physically realizable. A new realizable
    operation may legitimately refine the old observational equivalence relation.
    """
    operation = parse_operation(operation_spec)
    projection = analyze_projection(candidate_spec)
    report: dict[str, object] = {
        "candidate_id": projection["candidate_id"],
        "candidate_sha256": projection["candidate_sha256"],
        "operation_id": operation.id, "operation_sha256": digest(operation_spec),
        "candidate_verdict": "unchanged", "status": "unsupported",
        "physical_admissibility": "unassessed", "empirical_status": "not_tested",
        "proof_status": "not_checked_by_this_command",
        "missing_bridges": projection["missing_bridges"],
        "scope": "supplied_quadratic_carrier_and_operation_only",
    }
    if "native_law" not in projection:
        return report
    model = parse_amplitude_algebra(projection["native_law"])
    report["native_law"] = model.specification()
    scalar = model.carrier == "integer_scalar"
    closed = not (scalar and isinstance(operation, IntegerMatrix) and operation.r != 0)
    report["carrier_closed"] = closed
    if not closed:
        report.update(status="outside_carrier", closure_witness={
            "input": [1, 0], "output": list(operation.apply((1, 0)))})
        return report
    if isinstance(operation, IntegerMatrix):
        p, q, r, s = operation.p, operation.q, operation.r, operation.s
        eta = model.imaginary_weight
        coefficients = {"a2": p * p + eta * r * r - 1,
                        "ab": 0 if scalar else 2 * (p * q + eta * r * s),
                        "b2": 0 if scalar else q * q + eta * s * s - eta}
        norm_preserved = all(value == 0 for value in coefficients.values())
        determinant = p * s - q * r
        reversible = abs(p) == 1 if scalar else abs(determinant) == 1
        additive = True
        report["weight_preservation"] = {"holds": norm_preserved,
            "reason": "exact_polynomial_defect_on_actual_carrier",
            "defect_coefficients": coefficients}
        report["reversibility"] = {"holds": reversible,
            "reason": "scalar_multiplier_is_unit" if scalar else "integer_determinant_is_unit",
            "scalar_multiplier": p, "ambient_determinant": determinant}
        report["additivity"] = {"holds": True, "reason": "integer_linear_formula"}
        report["pair_sum_weight"] = {"holds": norm_preserved,
            "reason": "additivity_reduces_pair_sum_to_individual_weight_identity"}
    else:
        norm_preserved, reversible, additive = True, True, scalar
        report["weight_preservation"] = {"holds": True, "reason": "real_sign_square_is_unchanged"}
        report["reversibility"] = {"holds": True, "reason": "same_formula_is_its_inverse"}
        report["additivity"] = {"holds": additive,
            "reason": "identity_on_scalar" if scalar else "explicit_counterexample"}
        report["pair_sum_weight"] = {"holds": scalar,
            "reason": "identity_on_scalar" if scalar else "explicit_counterexample"}
        if not scalar:
            x, y = (1, 0), (1, 1)
            report["coherent_witness"] = {"left": list(x), "right": list(y),
                "map_of_sum": list(operation.apply(model.add(x, y))),
                "sum_of_maps": list(model.add(operation.apply(x), operation.apply(y))),
                "initial_weight": model.weight(model.add(x, y)),
                "transformed_weight": model.weight(model.add(operation.apply(x), operation.apply(y)))}
    report["multiplicativity_diagnostic_only"] = _multiplicativity(model, operation)
    report["old_quotient_stability"] = _quotient(model, operation, projection)
    report["supplied_contracts"] = {
        "closed_reversible_weight": closed and reversible and norm_preserved,
        "coherent_reversible_weight": closed and reversible and norm_preserved and additive,
        "meaning": "optional_contracts_not_derived_physical_requirements",
        "multiplicativity_is_required": False,
    }
    report["status"] = "analyzed"
    return report
