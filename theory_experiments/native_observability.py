"""Exact tests of a specified scalar projection, never global candidate rejection."""

from __future__ import annotations

import hashlib
from pathlib import Path

from theory_experiments.amplitude_algebra import (
    AmplitudeAlgebra,
    resolve_source_algebra,
)
from theory_experiments.candidate_pipeline import digest, parse_hypothesis
from theory_experiments.source_candidate import SourceCandidate

GRAMMAR = ("integer_coordinate_constants", "amplitude_variables", "addition", "multiplication", "terminal_weight")
LOADED_MODULE_SHA256 = hashlib.sha256(Path(__file__).read_bytes()).hexdigest()


def analyze_projection(specification: object) -> dict[str, object]:
    """Analyze pi(a,b)=a for the supplied quadratic integer algebra only.

    For a dual algebra pi is an algebra homomorphism and W=pi^2, hence all
    finite expressions in GRAMMAR have identical terminal weight after pi.
    Other transformations, physical preparations and measurements are not
    supplied. A projection counterexample does not reject a candidate.
    """
    candidate = parse_hypothesis(specification)
    model: AmplitudeAlgebra | None = None
    missing_bridges: list[str] = []
    if isinstance(candidate, AmplitudeAlgebra):
        model = candidate
    elif isinstance(candidate, SourceCandidate):
        resolved = resolve_source_algebra(candidate)
        model = None if resolved is None else resolved[0]
        missing_bridges = list(candidate.missing_bridges)
    report: dict[str, object] = {
        "candidate_id": candidate.id, "candidate_sha256": digest(candidate.specification()),
        "status": "unsupported", "candidate_verdict": "unchanged",
        "projection": "pi(a,b)=a_to_integer_scalar_with_weight_a_squared",
        "grammar": list(GRAMMAR), "missing_bridges": missing_bridges,
        "evidence_kind": "exact_coefficients_or_explicit_projection_counterexample",
        "proof_status": "not_checked_by_this_command", "empirical_status": "not_tested",
        "untested": ["physical_preparability", "additional_transformations", "detector_readout",
                     "physical_tensor_composites", "QM", "SM", "gravity"],
    }
    if model is None or model.weight_rule != "quadratic":
        report["reason"] = "requires_reviewed_quadratic_integer_algebra_adapter"
        return report

    k, eta = model.product_square, model.imaginary_weight
    report["native_law"] = model.specification()
    # Exact polynomial coefficients, not a sample-based universal claim.
    # W(x*y)-W(x)W(y) = A*a*b*c*d + B*b*b*d*d.
    report["weight_law_coefficients"] = {"abcd": 2 * (k + eta), "b2d2": k * k - eta * eta}
    report["quadratic_law_compatibility"] = {
        "nonnegative_on_integer_carrier": eta >= 0,
        "multiplicative_on_integer_carrier": 2 * (k + eta) == 0 and k * k - eta * eta == 0,
        "scope": "supplied_integer_quadratic_algebra_not_empirical_compatibility",
    }
    if model.carrier == "integer_scalar" or (k == 0 and eta == 0):
        report["status"] = "preserves_declared_grammar"
        report["relation"] = "identity" if model.carrier == "integer_scalar" else "many_to_one_weight_preserving_quotient"
        report["projection_identity_coefficients"] = {"multiplication_bd": k, "weight_b2": eta}
        report["conclusion_scope"] = "all_finite_expressions_in_declared_grammar_only"
        return report

    unit = (0, 1)
    # The witness is deliberately evaluated via the native implementation,
    # independently of the coefficient classification above.
    expression: dict[str, object] = {"variable": 0}
    if eta != 0:
        actual = model.weight(unit)
    else:
        expression = {"multiply": [{"variable": 0}, {"variable": 0}]}
        actual = model.weight(model.multiply(unit, unit))
    if actual == 0:
        raise ValueError("projection witness disagrees with coefficient analysis; checker error")
    report["status"] = "projection_counterexample"
    report["witness"] = {"environment": [[0, 1]], "expression": expression,
                         "native_weight": str(actual), "projected_scalar_weight": "0",
                         "initial_native_weight": str(model.weight(unit))}
    report["conclusion_scope"] = "this_projection_fails_not_all_representations_or_the_candidate"
    return report
