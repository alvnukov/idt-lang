"""Deterministic finite reference witnesses, not primitive or empirical rejection."""

from __future__ import annotations

import hashlib
from dataclasses import dataclass

from theory_experiments.amplitude_algebra import (
    AmplitudeAlgebra,
    parse_amplitude_algebra,
    resolve_source_algebra,
)
from theory_experiments.native_bell_bridge import (
    BRIDGE,
    MISSING_BRIDGES,
    NativeBellBridge,
    evaluate_native_bell_bridge,
)
from theory_experiments.native_readout_probe import (
    ASSUMPTIONS as READOUT_ASSUMPTIONS,
)
from theory_experiments.native_readout_probe import (
    RESPONSES,
    NativeReadoutProbe,
    evaluate_response_on_native_trace,
)
from theory_experiments.primitive_screen import (
    Check,
    Limits,
    Status,
    aggregate_status,
    bounded_int,
    candidate_id,
    canonical_json,
    exact_fraction,
    object_fields,
)
from theory_experiments.source_candidate import SourceCandidate, parse_source_candidate

ORDERING = "ascending_(max(abs(x),abs(y)),abs(x)+abs(y),x,y)_full_signed_square_no_pruning"
IDENTITY = ((1, 0), (0, 1))
HADAMARD = ((1, 1), (1, -1))
ASSUMPTIONS = READOUT_ASSUMPTIONS + (
    "only_real_integer_reference_preparations_C(x,y)_equals_[[x,y],[1,0]]",
    "alice_I_I_bob_I_H_are_supplied_not_derived_physical_operations",
    "H_determinant_minus_two_not_a_proved_physical_reversible_map",
    "first_witness_means_first_only_in_declared_finite_enumeration",
    "finite_exhaustion_is_not_universal_reference_invariance_or_QM_proof",
)


@dataclass(frozen=True)
class NativeReadoutSearch:
    id: str
    model: AmplitudeAlgebra | SourceCandidate
    radius: int
    responses: tuple[str, ...]

    def __post_init__(self) -> None:
        candidate_id(self.id)
        if not isinstance(self.model, (AmplitudeAlgebra, SourceCandidate)):
            raise TypeError("model must be amplitude_algebra or source_theory")
        bounded_int(self.radius, 0, 4)
        if not isinstance(self.responses, tuple) or not 1 <= len(self.responses) <= 3:
            raise ValueError("responses must contain 1 to 3 ordered unique names")
        for response in self.responses:
            candidate_id(response)
        if len(set(self.responses)) != len(self.responses):
            raise ValueError("duplicate response")

    def specification(self) -> dict[str, object]:
        return {"id": self.id, "family": "native_readout_search", "model": self.model.specification(),
                "radius": self.radius, "responses": list(self.responses)}


def parse_native_readout_search(value: object) -> NativeReadoutSearch:
    row = object_fields(value, {"id", "family", "model", "radius", "responses"})
    if row["family"] != "native_readout_search":
        raise ValueError("expected native_readout_search")
    raw = object_fields(row["model"])
    model: AmplitudeAlgebra | SourceCandidate
    if raw.get("family") == "amplitude_algebra":
        model = parse_amplitude_algebra(raw)
    elif raw.get("family") == "source_theory":
        model = parse_source_candidate(raw)
    else:
        raise ValueError("model must be amplitude_algebra or source_theory")
    responses = row["responses"]
    if not isinstance(responses, list) or not 1 <= len(responses) <= 3:
        raise ValueError("responses must contain 1 to 3 ordered unique names")
    return NativeReadoutSearch(candidate_id(row["id"]), model, bounded_int(row["radius"], 0, 4),
                               tuple(candidate_id(response) for response in responses))


def reference_preparations(radius: int) -> tuple[tuple[int, int], ...]:
    """The complete signed square in the public deterministic order."""
    bounded_int(radius, 0, 4)
    return tuple(sorted(((x, y) for x in range(-radius, radius + 1) for y in range(-radius, radius + 1)),
                        key=lambda pair: (max(abs(pair[0]), abs(pair[1])), abs(pair[0]) + abs(pair[1]), *pair)))


def evaluate_native_readout_search(
    search: NativeReadoutSearch, limits: Limits,
) -> tuple[tuple[Check, ...], dict[str, object]]:
    domain = reference_preparations(search.radius)
    planned = 4 * len(domain)
    rows: list[dict[str, object]] = [
        {"response": response, "state": "inconclusive", "preparations_checked": 0, "first_witness": None}
        for response in search.responses]
    scope: dict[str, object] = {
        "adapter_status": "bounded_reference_family_selected_response_search",
        "candidate_verdict": "unchanged", "scientific_status": "unassessed",
        "execution_status": "unsupported", "search_complete": False, "domain_exhausted": False,
        "stop_reason": "preflight", "ordering": ORDERING,
        "domain": {"radius": search.radius, "preparations": len(domain),
                   "preparation": "C(x,y)=[[x,y],[1,0]]_real_integer_amplitudes",
                   "alice": [[list(row) for row in IDENTITY] for _ in range(2)],
                   "bob": [[list(row) for row in matrix] for matrix in (IDENTITY, HADAMARD)]},
        "responses": rows, "unused_limits": ["coefficient_radius", "reference_radius", "max_copies"],
        "model_sha256": hashlib.sha256(canonical_json(search.model.specification()).encode()).hexdigest(),
        "native_protocol_metadata": None,
        "supplied_assumptions": list(ASSUMPTIONS), "missing_bridges": list(MISSING_BRIDGES),
        "witness_criterion": "Alice_outcome_1_reference_row_marginal_Bob_I_minus_Bob_H_is_nonzero",
        "witness_scope": "conditional_selected_operational_package_incompatibility_not_primitive_rejection",
        "first_witness_scope": "minimal_only_in_declared_bounded_enumeration_not_all_possible_experiments",
        "proof_status": "not_attempted", "proof_check": "not_run_by_this_evaluator", "empirical_status": "not_tested",
        "proof_artifact": "Proofs/QMClosure/NativeReadoutSelection.lean",
        "artifact_relation": "reference_counterexample_refutes_invariance_not_formal_Python_verification",
        "scope_boundary": "no_physical_accessibility_or_Gaussian_off_real_or_continuous_classification_no_full_QM_SM_or_gravity",
    }
    checked = 0

    def finish(status: Status) -> tuple[tuple[Check, ...], dict[str, object]]:
        scope["budget"] = {"unit": "native_joint_context", "maximum": limits.max_cases,
                           "checked": checked, "planned": planned, "contexts_per_atomic_preparation": 4,
                           "preparations_checked": checked // 4}
        return (Check("native_readout_search_completion_only", status, checked, planned,
                      "bounded_search_execution_not_primitive_or_physical_acceptance", ASSUMPTIONS, None),), scope

    # Preflight uses the existing exact full-spec binding, never retained source execution.
    if any(response not in RESPONSES for response in search.responses):
        scope.update(unsupported_reason="unknown_selected_response", stop_reason="unsupported_preflight")
        return finish("unsupported")
    model = search.model if isinstance(search.model, AmplitudeAlgebra) else None
    scope["model_origin"] = "explicit_supplied_algebra"
    if isinstance(search.model, SourceCandidate):
        resolved = resolve_source_algebra(search.model)
        scope.update(model_origin="unbound_source_snapshot", source_missing_bridges=list(search.model.missing_bridges),
                     source_boundary="exact_full_spec_binding_not_source_execution_or_checked_proof")
        if resolved is not None:
            model, key = resolved
            scope.update(model_origin="exact_archived_source_specification_binding", source_specification_sha256=key)
    if model is None:
        scope.update(unsupported_reason="missing_exact_reviewed_source_binding", stop_reason="unsupported_preflight")
        return finish("unsupported")
    if model.weight_rule != "quadratic" or model.imaginary_weight < 0:
        scope.update(unsupported_reason="normalized_weight_adapter_requires_quadratic_nonnegative_eta",
                     stop_reason="unsupported_preflight")
        return finish("unsupported")

    # ponytail: at most 81 preparations; retain only first witnesses, not a trace archive.
    trace_limits = Limits(max_cases=4, coefficient_radius=limits.coefficient_radius,
                          reference_radius=limits.reference_radius, max_copies=limits.max_copies)
    for index, (x, y) in enumerate(domain, 1):
        if checked + 4 > limits.max_cases:
            scope.update(execution_status="incomplete", stop_reason="budget_exhausted")
            return finish("inconclusive")
        protocol = NativeBellBridge("readout_reference_protocol", BRIDGE, search.model,
                                    (((x, 0), (y, 0)), ((1, 0), (0, 0))),
                                    (IDENTITY, IDENTITY), (IDENTITY, HADAMARD))
        native_checks, native = evaluate_native_bell_bridge(protocol, trace_limits)
        native_status = aggregate_status(native_checks)
        if native_status != "no_counterexample_within_bounds":
            # A valid supported real reference always has a positive reference weight.
            raise ValueError("preflight-supported reference failed native execution: checker error")
        checked += 4
        if index == 1:
            scope["native_protocol_metadata"] = {key: value for key, value in native.items()
                if key not in ("contexts", "no_signalling_diagnostic", "chsh", "uniform_setting_game_win",
                               "budget", "common_scale_scope_countercontrol", "preparation_raw_total")}
        for row in rows:
            if row["first_witness"] is not None:
                continue
            response = row["response"]
            assert isinstance(response, str)
            probe = NativeReadoutProbe("readout_reference_probe", protocol, response)
            response_checks, selected = evaluate_response_on_native_trace(probe, trace_limits, native_checks, native)
            if aggregate_status(response_checks) != "no_counterexample_within_bounds":
                raise ValueError("supported positive response failed execution: checker error")
            row["preparations_checked"] = index
            contexts = selected["response_contexts"]
            if not isinstance(contexts, list) or len(contexts) != 4:
                raise ValueError("selected response contexts missing: checker error")
            marginals = [object_fields(contexts[i])["alice_marginal"] for i in (0, 1)]
            if any(not isinstance(marginal, list) or len(marginal) != 2 for marginal in marginals):
                raise ValueError("reference row marginal missing: checker error")
            before_row, after_row = marginals
            assert isinstance(before_row, list) and isinstance(after_row, list)
            before, after = exact_fraction(before_row[1]), exact_fraction(after_row[1])
            if before != after:
                row.update(state="conditional_violation_found", first_witness={
                    "preparation_index": index, "coordinates": [x, y],
                    "probe": probe.specification(), "limits": trace_limits.specification(),
                    "selected_response_checks": [check.specification() for check in response_checks],
                    "selected_response_evidence": selected,
                    "reference_row": {"before": str(before), "after": str(after),
                                      "difference_before_minus_after": str(before - after)}})
        scope["domain_exhausted"] = index == len(domain)
        if all(row["first_witness"] is not None for row in rows):
            scope.update(execution_status="complete", search_complete=True, stop_reason="all_witnesses_found")
            return finish("no_counterexample_within_bounds")
    for row in rows:
        if row["first_witness"] is None:
            row["state"] = "no_violation_within_bounds"
    scope.update(execution_status="complete", search_complete=True, stop_reason="domain_exhausted")
    return finish("no_counterexample_within_bounds")
