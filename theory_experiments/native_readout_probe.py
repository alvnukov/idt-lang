"""Selected detector responses over an unchanged, validated native Bell trace."""

from __future__ import annotations

import hashlib
from dataclasses import dataclass
from fractions import Fraction

from theory_experiments.native_bell_bridge import (
    MISSING_BRIDGES,
    NativeBellBridge,
    evaluate_native_bell_bridge,
    parse_native_bell_bridge,
)
from theory_experiments.primitive_screen import (
    Check,
    Limits,
    Status,
    bounded_int,
    candidate_id,
    canonical_json,
    exact_fraction,
    object_fields,
)

RESPONSES = ("native_weight", "squared_native_weight", "spike_49")
ASSUMPTIONS = (
    "native_trace_and_source_binding_inherited_from_supplied_native_bell_protocol",
    "selected_detector_response_is_separate_from_original_native_weight",
    "entrywise_response_normalized_by_each_context_total_is_supplied",
    "arbitrary_preparation_accessibility_and_context_independent_response_are_not_derived",
    "absence_of_extra_hidden_apparatus_freedoms_is_a_supplied_model_restriction",
    "no_signalling_is_a_conditional_diagnostic_not_a_primitive_rejection_requirement",
    "completion_only_not_scientific_acceptance_or_physical_realizability",
)


@dataclass(frozen=True)
class NativeReadoutProbe:
    id: str
    protocol: NativeBellBridge
    response: str

    def __post_init__(self) -> None:
        candidate_id(self.id)
        candidate_id(self.response)
        if not isinstance(self.protocol, NativeBellBridge):
            raise TypeError("protocol must be a full native_bell_bridge specification")

    def specification(self) -> dict[str, object]:
        return {"id": self.id, "family": "native_readout_probe",
                "protocol": self.protocol.specification(), "response": self.response}


def parse_native_readout_probe(value: object) -> NativeReadoutProbe:
    row = object_fields(value, {"id", "family", "protocol", "response"})
    if row["family"] != "native_readout_probe":
        raise ValueError("expected native_readout_probe")
    return NativeReadoutProbe(candidate_id(row["id"]), parse_native_bell_bridge(row["protocol"]),
                              candidate_id(row["response"]))


def _response(weight: Fraction, response: str) -> Fraction:
    if response == "native_weight":
        return weight
    if response == "squared_native_weight":
        return weight * weight
    if response == "spike_49":
        return weight + (1 if weight == 49 else 0)
    raise ValueError("unsupported response reached computation: checker error")


def _selected_weights(context: dict[str, object], response: str) -> list[list[Fraction]]:
    raw = context["raw_weights"]
    if not isinstance(raw, list) or len(raw) != 2:
        raise ValueError("native trace must contain two weight rows: checker error")
    weights: list[list[Fraction]] = []
    for row in raw:
        if not isinstance(row, list) or len(row) != 2:
            raise ValueError("native trace must contain two weights per row: checker error")
        values = [exact_fraction(value) for value in row]
        if any(value < 0 or value.denominator != 1 for value in values):
            raise ValueError("native trace weights must be nonnegative integers: checker error")
        weights.append([_response(value, response) for value in values])
    return weights


def evaluate_native_readout_probe(probe: NativeReadoutProbe, limits: Limits) -> tuple[tuple[Check, ...], dict[str, object]]:
    scope: dict[str, object] = {
        "adapter_status": "selected_response_over_validated_native_trace",
        "candidate_verdict": "unchanged", "scientific_status": "unassessed",
        "execution_status": "unsupported", "response": probe.response,
        "response_definitions": {"native_weight": "f(W)=W", "squared_native_weight": "f(W)=W^2",
                                 "spike_49": "f(W)=W+1_if_W_equals_49_else_W"},
        "universal_classifier_hypotheses_not_checked": [
            "all_integer_reference_preparation_accessibility", "physical_H_and_local_action_admissibility",
            "entrywise_context_independent_globally_normalized_response",
            "absence_of_extra_hidden_apparatus_freedoms", "universal_reference_row_invariance"],
        "protocol_sha256": hashlib.sha256(canonical_json(probe.protocol.specification()).encode()).hexdigest(),
        "protocol_hash_excludes_selected_response": True,
        "original_native_weight_semantics": "unchanged_not_replaced_by_selected_response",
        "native_protocol_evidence": None,
        "native_protocol_evidence_readout": "separate_reference_native_weight_not_selected_detector_response",
        "supplied_assumptions": list(ASSUMPTIONS), "missing_bridges": list(MISSING_BRIDGES),
        "response_contexts": [], "proof_status": "not_attempted",
        "proof_check": "not_run_by_this_evaluator", "empirical_status": "not_tested",
        "proof_artifact": "Proofs/QMClosure/NativeReadoutSelection.lean",
        "artifact_relation": "conditional_integer_response_theorem_not_formal_Python_verification",
        "scope_boundary": "no_Gaussian_off_real_or_continuous_response_classification_no_full_QM_SM_or_gravity",
        "budget": {"unit": "joint_context", "maximum": limits.max_cases, "checked": 0, "planned": 4},
    }

    def finish(status: Status, checked: int = 0) -> tuple[tuple[Check, ...], dict[str, object]]:
        scope["budget"] = {"unit": "joint_context", "maximum": limits.max_cases, "checked": checked, "planned": 4}
        return (Check("native_readout_execution_completion_only", status, checked, 4,
                      "four_selected_response_contexts_executed_not_a_physical_target", ASSUMPTIONS, None),), scope

    if probe.response not in RESPONSES:
        scope["unsupported_reason"] = "unknown_selected_response"
        return finish("unsupported")
    checks, native = evaluate_native_bell_bridge(probe.protocol, limits)
    scope["native_protocol_evidence"] = native
    if checks[0].status != "no_counterexample_within_bounds":
        scope["execution_status"] = native["execution_status"]
        for key in ("unsupported_reason", "incomplete_reason"):
            if key in native:
                scope[key] = native[key]
        return finish(checks[0].status)
    trace = native["contexts"]
    if not isinstance(trace, list) or len(trace) != 4:
        raise ValueError("complete native trace must contain four contexts: checker error")
    contexts: list[dict[str, object]] = []
    correlations: list[Fraction] = []
    wins: list[Fraction] = []
    alice: list[list[Fraction]] = []
    bob: list[list[Fraction]] = []
    for index, entry in enumerate(trace):
        context = object_fields(entry)
        x, y = bounded_int(context["x"], 0, 1), bounded_int(context["y"], 0, 1)
        if (x, y) != divmod(index, 2):
            raise ValueError("native trace context order mismatch: checker error")
        weights = _selected_weights(context, probe.response)
        total = sum((sum(row, Fraction()) for row in weights), Fraction())
        if total <= 0:
            scope.update(execution_status="undefined_readout", incomplete_reason="zero_total_selected_response")
            return finish("inconclusive")
        probabilities = [[weight / total for weight in row] for row in weights]
        a = [sum(row, Fraction()) for row in probabilities]
        b = [probabilities[0][j] + probabilities[1][j] for j in range(2)]
        correlation = probabilities[0][0] - probabilities[0][1] - probabilities[1][0] + probabilities[1][1]
        win = sum((probabilities[i][j] for i in range(2) for j in range(2)
                   if (i ^ j) == x*y), Fraction())
        alice.append(a)
        bob.append(b)
        correlations.append(correlation)
        wins.append(win)
        contexts.append({"x": x, "y": y, "native_raw_weights": context["raw_weights"],
            "response_weights": [[str(value) for value in row] for row in weights], "response_total": str(total),
            "probabilities": [[str(value) for value in row] for row in probabilities],
            "alice_marginal": [str(value) for value in a], "bob_marginal": [str(value) for value in b],
            "correlation": str(correlation), "game_win": str(win)})
    alice_differences = [[alice[2*x][i] - alice[2*x+1][i] for i in range(2)] for x in range(2)]
    bob_differences = [[bob[y][j] - bob[2+y][j] for j in range(2)] for y in range(2)]
    holds = all(value == 0 for pair in alice_differences + bob_differences for value in pair)
    scope.update(execution_status="complete", response_contexts=contexts,
        chsh=str(correlations[0] + correlations[1] + correlations[2] - correlations[3]),
        uniform_setting_game_win=str(sum(wins, Fraction()) / 4),
        no_signalling_diagnostic={"holds": holds,
            "alice_marginal_differences_y0_minus_y1": [[str(value) for value in row] for row in alice_differences],
            "bob_marginal_differences_x0_minus_x1": [[str(value) for value in row] for row in bob_differences],
            "meaning": ("compatible_on_four_supplied_contexts_not_universal_or_physical_acceptance" if holds else
                        "conditional_incompatibility_of_selected_response_and_supplied_operations_not_primitive_rejection")})
    return finish("no_counterexample_within_bounds", 4)
