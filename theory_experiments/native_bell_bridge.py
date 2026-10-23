"""Supplied integer local action and normalized weight, not derived Bell physics."""

from __future__ import annotations

import hashlib
from dataclasses import dataclass
from fractions import Fraction
from typing import TypeAlias

from theory_experiments.amplitude_algebra import (
    Amplitude,
    AmplitudeAlgebra,
    parse_amplitude_algebra,
    resolve_source_algebra,
)
from theory_experiments.primitive_screen import (
    Check,
    Limits,
    Status,
    bounded_int,
    candidate_id,
    canonical_json,
    object_fields,
)
from theory_experiments.source_candidate import SourceCandidate, parse_source_candidate

Matrix: TypeAlias = tuple[tuple[int, int], tuple[int, int]]
State: TypeAlias = tuple[tuple[Amplitude, Amplitude], tuple[Amplitude, Amplitude]]
BRIDGE = "integer_local_normalized_weight_v1"
ASSUMPTIONS = (
    "supplied_native_algebra_not_derived_from_lower_IDT_primitives",
    "supplied_2x2_composite_preparation_not_derived_tensor_closure",
    "supplied_local_integer_matrix_action_D_equals_A_C_B_transpose",
    "supplied_outcome_labels_and_p_equals_native_weight_over_total",
    "supplied_settings_and_preparability_not_physical_realizability",
    "uniform_setting_game_win_is_descriptive_not_a_dataset_test",
    "completion_only_not_candidate_rejection_ranking_or_QM_derivation",
)
MISSING_BRIDGES = (
    "source_derived_map_from_same_symbolic_preparation_and_settings_to_operations",
    "physical_composite_preparation_and_local_action_admissibility",
    "native_weight_to_physical_probability_and_outcome_interpretation",
    "settings_choice_and_joint_physical_preparability",
)


def _pair(value: object) -> tuple[object, object]:
    if not isinstance(value, (list, tuple)) or len(value) != 2:
        raise ValueError("expected exactly two entries")
    return value[0], value[1]


def _amplitude(value: object) -> Amplitude:
    a, b = _pair(value)
    return bounded_int(a, -4, 4), bounded_int(b, -4, 4)


def _matrix(value: object) -> Matrix:
    first, second = _pair(value)
    p, q = _pair(first)
    r, s = _pair(second)
    return ((bounded_int(p, -4, 4), bounded_int(q, -4, 4)),
            (bounded_int(r, -4, 4), bounded_int(s, -4, 4)))


def _state(value: object) -> State:
    first, second = _pair(value)
    a, b = _pair(first)
    c, d = _pair(second)
    return ((_amplitude(a), _amplitude(b)), (_amplitude(c), _amplitude(d)))


@dataclass(frozen=True)
class NativeBellBridge:
    id: str
    bridge: str
    model: AmplitudeAlgebra | SourceCandidate
    preparation: State
    alice: tuple[Matrix, Matrix]
    bob: tuple[Matrix, Matrix]

    def __post_init__(self) -> None:
        candidate_id(self.id)
        candidate_id(self.bridge)
        if not isinstance(self.model, (AmplitudeAlgebra, SourceCandidate)):
            raise TypeError("model must be amplitude_algebra or source_theory, never a nested bridge")
        _state(self.preparation)
        for party in (self.alice, self.bob):
            for matrix in _pair(party):
                _matrix(matrix)

    def specification(self) -> dict[str, object]:
        return {"id": self.id, "family": "native_bell_bridge", "bridge": self.bridge,
                "model": self.model.specification(),
                "preparation": [[list(cell) for cell in row] for row in self.preparation],
                "alice": [[list(row) for row in matrix] for matrix in self.alice],
                "bob": [[list(row) for row in matrix] for matrix in self.bob]}


def parse_native_bell_bridge(value: object) -> NativeBellBridge:
    row = object_fields(value, {"id", "family", "bridge", "model", "preparation", "alice", "bob"})
    if row["family"] != "native_bell_bridge":
        raise ValueError("expected native_bell_bridge")
    raw = object_fields(row["model"])
    model: AmplitudeAlgebra | SourceCandidate
    if raw.get("family") == "amplitude_algebra":
        model = parse_amplitude_algebra(raw)
    elif raw.get("family") == "source_theory":
        model = parse_source_candidate(raw)
    else:
        raise ValueError("model must be amplitude_algebra or source_theory, never a nested bridge")
    a0, a1 = _pair(row["alice"])
    b0, b1 = _pair(row["bob"])
    return NativeBellBridge(candidate_id(row["id"]), candidate_id(row["bridge"]), model,
                            _state(row["preparation"]), (_matrix(a0), _matrix(a1)),
                            (_matrix(b0), _matrix(b1)))


def _matrix_diagnostic(matrix: Matrix) -> dict[str, object]:
    (p, q), (r, s) = matrix
    gram = ((p*p + r*r, p*q + r*s), (p*q + r*s, q*q + s*s))
    scale = gram[0][0]
    scaled = scale > 0 and gram[0][1] == 0 and gram[1][1] == scale
    determinant = p*s - q*r
    return {"matrix": [list(row) for row in matrix], "gram": [list(row) for row in gram],
            "positive_scaled_isometry": scaled, "weight_scale": scale if scaled else None,
            "exact_norm_preserved": scaled and scale == 1,
            "integer_determinant": determinant, "integer_lattice_bijection": abs(determinant) == 1,
            "integer_inverse_exists": abs(determinant) == 1,
            "transpose_projective_inverse_scale": scale if scaled else None,
            "reversibility_meaning": "readout_projective_only_not_physical_reversibility"}


def _sum(model: AmplitudeAlgebra, terms: list[Amplitude]) -> Amplitude:
    total = (0, 0)
    for term in terms:
        total = model.add(total, term)
    return total


def _act(model: AmplitudeAlgebra, state: State, alice: Matrix, bob: Matrix) -> State:
    # Matrix entries embed as native real integer amplitudes: no scalar extension.
    def cell(i: int, j: int) -> Amplitude:
        return _sum(model, [model.multiply(model.multiply((alice[i][k], 0), state[k][l]),
                                          (bob[j][l], 0))
                            for k in range(2) for l in range(2)])
    return ((cell(0, 0), cell(0, 1)), (cell(1, 0), cell(1, 1)))


def _scale_scope(model: AmplitudeAlgebra) -> dict[str, object]:
    # Two *modes*, each holding a real native amplitude; r is a fixed reference.
    reference = ((0, 0), (1, 0))
    records: list[dict[str, object]] = []
    for scale in (1, 2):
        vector = (model.multiply((scale, 0), (1, 0)), (0, 0))
        direct = [model.weight(value) for value in vector]
        continued = [model.weight(model.add(value, ref)) for value, ref in zip(vector, reference, strict=True)]
        records.append({"scale": scale, "direct_raw_weights": [str(x) for x in direct],
            "direct_probabilities": [str(Fraction(x, sum(direct))) for x in direct],
            "fixed_reference_raw_weights": [str(x) for x in continued],
            "fixed_reference_probabilities": [str(Fraction(x, sum(continued))) for x in continued]})
    return {"two_mode_reference": [[0, 0], [1, 0]], "evaluations": records,
            "conclusion": "common_scale_invariance_only_for_homogeneous_continuations_not_global_quotient",
            "old_raw_weight_semantics": "unchanged_and_scale_sensitive"}


def evaluate_native_bell_bridge(bridge: NativeBellBridge, limits: Limits) -> tuple[tuple[Check, ...], dict[str, object]]:
    scope: dict[str, object] = {
        "adapter_status": "supplied_native_integer_local_normalized_weight",
        "candidate_verdict": "unchanged", "scientific_status": "unassessed",
        "execution_status": "unsupported", "bridge": bridge.bridge,
        "model_sha256": hashlib.sha256(canonical_json(bridge.model.specification()).encode()).hexdigest(),
        "supplied_assumptions": list(ASSUMPTIONS), "missing_bridges": list(MISSING_BRIDGES),
        "artifact_relation": "Lean_proves_separate_mathematical_statements_not_formal_Python_verification",
        "proof_check": "not_run_by_this_evaluator",
        "proof_artifact": "Proofs/QMClosure/NativeBellScaledBridge.lean",
        "probability_interpretation": "supplied_Fraction_native_weight_over_context_total",
        "scalar_amplitude_extension": False, "empirical_status": "not_tested",
        "contexts": [], "unused_limits": ["coefficient_radius", "reference_radius", "max_copies"],
        "budget": {"unit": "joint_context", "maximum": limits.max_cases, "checked": 0, "planned": 4},
    }

    def finish(status: str, checked: int = 0) -> tuple[tuple[Check, ...], dict[str, object]]:
        # Explicit branches keep the public Check status type narrow.
        result: Status = ("unsupported" if status == "unsupported" else "inconclusive"
                          if status == "inconclusive" else "no_counterexample_within_bounds")
        scope["budget"] = {"unit": "joint_context", "maximum": limits.max_cases, "checked": checked, "planned": 4}
        return (Check("native_bell_execution_completion_only", result, checked, 4,
                      "four_supplied_contexts_executed_not_a_Bell_target", ASSUMPTIONS, None),), scope

    model: AmplitudeAlgebra | None = None
    if isinstance(bridge.model, AmplitudeAlgebra):
        model = bridge.model
        scope["model_origin"] = "explicit_supplied_algebra"
    else:
        resolved = resolve_source_algebra(bridge.model)
        scope.update(model_origin="unbound_source_snapshot", source_missing_bridges=list(bridge.model.missing_bridges),
                     source_boundary="exact_full_spec_binding_not_source_execution_or_checked_proof")
        if resolved is not None:
            model, key = resolved
            scope.update(model_origin="exact_archived_source_specification_binding", source_specification_sha256=key)
    reason: str | None = None
    if bridge.bridge != BRIDGE:
        reason = "unknown_bridge"
    elif model is None:
        reason = "missing_exact_reviewed_source_binding"
    elif model.weight_rule != "quadratic" or model.imaginary_weight < 0:
        reason = "normalized_weight_adapter_requires_quadratic_nonnegative_eta"
    elif model.carrier == "integer_scalar" and any(a[1] for row in bridge.preparation for a in row):
        reason = "preparation_outside_integer_scalar_carrier"
    if reason is not None:
        scope["unsupported_reason"] = reason
        return finish("unsupported")
    assert model is not None
    scope["native_law"] = model.specification()
    operations = {party: [_matrix_diagnostic(matrix) for matrix in matrices]
                  for party, matrices in (("alice", bridge.alice), ("bob", bridge.bob))}
    scope["operations"] = operations
    if any(not row["positive_scaled_isometry"] for matrices in operations.values() for row in matrices):
        scope["unsupported_reason"] = "operation_not_positive_scaled_isometry_for_this_bridge"
        return finish("unsupported")
    if limits.max_cases < 4:
        scope.update(execution_status="incomplete", incomplete_reason="atomic_four_context_budget_required")
        return finish("inconclusive")
    initial_weight = sum(model.weight(value) for row in bridge.preparation for value in row)
    scope["preparation_raw_total"] = str(initial_weight)
    if initial_weight == 0:
        scope.update(execution_status="undefined_readout", incomplete_reason="zero_total_native_weight")
        return finish("inconclusive")
    contexts: list[dict[str, object]] = []
    correlations: list[Fraction] = []
    wins: list[Fraction] = []
    alice_marginals: list[tuple[Fraction, Fraction]] = []
    bob_marginals: list[tuple[Fraction, Fraction]] = []
    for x in range(2):
        for y in range(2):
            state = _act(model, bridge.preparation, bridge.alice[x], bridge.bob[y])
            weights = [[model.weight(value) for value in row] for row in state]
            total = sum(sum(row) for row in weights)
            if total <= 0:
                raise ValueError("positive scaled quadratic adapter produced nonpositive total: checker error")
            probabilities = [[Fraction(value, total) for value in row] for row in weights]
            correlation = sum(((-1 if i != j else 1) * probabilities[i][j]
                               for i in range(2) for j in range(2)), Fraction())
            win = sum((probabilities[i][j] for i in range(2) for j in range(2)
                       if (i ^ j) == x*y), Fraction())
            correlations.append(correlation)
            wins.append(win)
            alice_marginal = (sum(probabilities[0], Fraction()), sum(probabilities[1], Fraction()))
            bob_marginal = (probabilities[0][0] + probabilities[1][0],
                            probabilities[0][1] + probabilities[1][1])
            alice_marginals.append(alice_marginal)
            bob_marginals.append(bob_marginal)
            contexts.append({"x": x, "y": y, "state": [[list(a) for a in row] for row in state],
                "raw_weights": [[str(a) for a in row] for row in weights], "raw_total": str(total),
                "probabilities": [[str(a) for a in row] for row in probabilities],
                "alice_marginal": [str(value) for value in alice_marginal],
                "bob_marginal": [str(value) for value in bob_marginal],
                "correlation": str(correlation), "game_win": str(win)})
    chsh = correlations[0] + correlations[1] + correlations[2] - correlations[3]
    alice_differences = [[alice_marginals[2*x][i] - alice_marginals[2*x+1][i]
                          for i in range(2)] for x in range(2)]
    bob_differences = [[bob_marginals[y][j] - bob_marginals[2+y][j]
                        for j in range(2)] for y in range(2)]
    no_signalling = {
        "holds": all(value == 0 for pair in alice_differences + bob_differences for value in pair),
        "alice_marginal_differences_y0_minus_y1": [[str(value) for value in pair] for pair in alice_differences],
        "bob_marginal_differences_x0_minus_x1": [[str(value) for value in pair] for pair in bob_differences],
        "scope": "exact_four_supplied_context_diagnostic_not_physical_admissibility_or_rejection_requirement",
    }
    scope.update(execution_status="complete", contexts=contexts, chsh=str(chsh),
                 uniform_setting_game_win=str(sum(wins, Fraction()) / 4),
                 no_signalling_diagnostic=no_signalling,
                 common_scale_scope_countercontrol=_scale_scope(model))
    return finish("complete", 4)
