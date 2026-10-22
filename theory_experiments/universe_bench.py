"""A bounded supplied two-path protocol, not a physical world or detector law."""

from __future__ import annotations

import hashlib
import itertools
from collections.abc import Iterator
from dataclasses import dataclass

from theory_experiments.amplitude_algebra import (
    Amplitude,
    AmplitudeAlgebra,
    parse_amplitude_algebra,
    resolve_source_algebra,
)
from theory_experiments.primitive_screen import (
    Check,
    Limits,
    bounded_int,
    candidate_id,
    canonical_json,
    object_fields,
)
from theory_experiments.source_candidate import SourceCandidate, parse_source_candidate

ASSUMPTIONS = (
    "supplied_carrier_product_weight_and_preparations_not_derived_from_IDT",
    "supplied_path_multiplication_additive_recombination_and_blocked_arm_deletion",
    "raw_weight_is_not_probability_or_a_derived_detector_law",
    "arithmetic_is_conditional_on_supplied_model_and_protocol",
    "execution_completion_is_not_a_model_selection_or_physical_validity_gate",
)
STEPS_PER_PREPARATION = 9
AMPLITUDE_FIELDS = ("left", "right", "left_factor", "right_factor")


def _amplitude(value: object) -> Amplitude:
    if not isinstance(value, (list, tuple)) or len(value) != 2:
        raise ValueError("amplitude requires two bounded integer coordinates")
    return bounded_int(value[0], -2, 2), bounded_int(value[1], -2, 2)


@dataclass(frozen=True)
class Preparation:
    id: str
    left: Amplitude
    right: Amplitude
    left_factor: Amplitude
    right_factor: Amplitude

    def __post_init__(self) -> None:
        candidate_id(self.id)
        for field in AMPLITUDE_FIELDS:
            _amplitude(getattr(self, field))

    def specification(self) -> dict[str, object]:
        return {"id": self.id, **{field: list(getattr(self, field)) for field in AMPLITUDE_FIELDS}}


@dataclass(frozen=True)
class UniverseBench:
    id: str
    scenario: str
    model: AmplitudeAlgebra | SourceCandidate
    preparations: tuple[Preparation, ...]

    def __post_init__(self) -> None:
        candidate_id(self.id)
        candidate_id(self.scenario)
        if not isinstance(self.model, (AmplitudeAlgebra, SourceCandidate)):
            raise TypeError("bench model grammar is amplitude_algebra or source_theory only")
        bounded_int(len(self.preparations), 1, 16)
        if len({prep.id for prep in self.preparations}) != len(self.preparations):
            raise ValueError("duplicate preparation id")

    def specification(self) -> dict[str, object]:
        return {"id": self.id, "family": "universe_bench", "scenario": self.scenario,
                "model": self.model.specification(),
                "preparations": [prep.specification() for prep in self.preparations]}


def parse_universe_bench(value: object) -> UniverseBench:
    row = object_fields(value, {"id", "family", "scenario", "model", "preparations"})
    if row["family"] != "universe_bench":
        raise ValueError("expected universe_bench")
    raw_model = object_fields(row["model"])
    model: AmplitudeAlgebra | SourceCandidate
    if raw_model.get("family") == "amplitude_algebra":
        model = parse_amplitude_algebra(raw_model)
    elif raw_model.get("family") == "source_theory":
        model = parse_source_candidate(raw_model)
    else:
        raise ValueError("bench model grammar is amplitude_algebra or source_theory only; no nested bench")
    raw_preps = row["preparations"]
    if not isinstance(raw_preps, list):
        raise TypeError("preparations must be an array")
    bounded_int(len(raw_preps), 1, 16)
    preparations: list[Preparation] = []
    for raw_prep in raw_preps:
        prep = object_fields(raw_prep, {"id", *AMPLITUDE_FIELDS})
        preparations.append(Preparation(candidate_id(prep["id"]), *(_amplitude(prep[field])
                                                                   for field in AMPLITUDE_FIELDS)))
    return UniverseBench(candidate_id(row["id"]), candidate_id(row["scenario"]), model, tuple(preparations))


def _steps(model: AmplitudeAlgebra, preparations: tuple[Preparation, ...]) -> Iterator[dict[str, object]]:
    """Lazy: stopping the iterator does not perform the following model operation."""
    for index, prep in enumerate(preparations):
        def event(operation: str, inputs: dict[str, object], output: object,
                  dependencies: list[str], operator_origin: str, prep_id: str = prep.id) -> dict[str, object]:
            return {"id": f"{prep_id}.{operation}", "preparation": prep_id, "operation": operation,
                    "inputs": inputs, "output": output, "dependencies": dependencies,
                    "operator_origin": operator_origin,
                    "result_origin": "supplied" if operation.startswith("prepare_") else "conditionally_computed"}

        left_ref, right_ref = f"{prep.id}.prepare_left", f"{prep.id}.prepare_right"
        left_product, right_product = f"{prep.id}.multiply_left", f"{prep.id}.multiply_right"
        yield event("prepare_left", {"field": f"preparations.{index}.left"}, list(prep.left), [],
                    "supplied_preparation")
        yield event("prepare_right", {"field": f"preparations.{index}.right"}, list(prep.right), [],
                    "supplied_preparation")
        left = model.multiply(prep.left, prep.left_factor)
        yield event("multiply_left", {"amplitude": list(prep.left), "factor": list(prep.left_factor),
                    "factor_field": f"preparations.{index}.left_factor"}, list(left), [left_ref],
                    "supplied_model.multiply")
        right = model.multiply(prep.right, prep.right_factor)
        yield event("multiply_right", {"amplitude": list(prep.right), "factor": list(prep.right_factor),
                    "factor_field": f"preparations.{index}.right_factor"}, list(right), [right_ref],
                    "supplied_model.multiply")
        total = model.add(left, right)
        yield event("add_paths", {"left": list(left), "right": list(right)}, list(total),
                    [left_product, right_product], "supplied_model.add")
        both = model.weight(total)
        yield event("weight_both", {"amplitude": list(total)}, str(both), [f"{prep.id}.add_paths"],
                    "supplied_model.weight")
        left_only = model.weight(left)
        yield event("weight_left_only", {"amplitude": list(left), "deleted_arm": "right"}, str(left_only),
                    [left_product], "supplied_model.weight_and_protocol_arm_deletion")
        right_only = model.weight(right)
        yield event("weight_right_only", {"amplitude": list(right), "deleted_arm": "left"}, str(right_only),
                    [right_product], "supplied_model.weight_and_protocol_arm_deletion")
        yield event("subtract_blocked_weights", {"both": str(both), "left_only": str(left_only),
                    "right_only": str(right_only)}, str(both - left_only - right_only),
                    [f"{prep.id}.weight_both", f"{prep.id}.weight_left_only", f"{prep.id}.weight_right_only"],
                    "supplied_protocol_interference_diagnostic")


def evaluate_universe_bench(bench: UniverseBench, limits: Limits) -> tuple[tuple[Check, ...], dict[str, object]]:
    planned = STEPS_PER_PREPARATION * len(bench.preparations)
    scope: dict[str, object] = {
        "adapter_status": "supplied_finite_two_path_protocol", "scientific_status": "unassessed",
        "candidate_verdict": "unchanged", "scenario": bench.scenario, "execution_status": "unsupported",
        "model_sha256": hashlib.sha256(canonical_json(bench.model.specification()).encode("utf-8")).hexdigest(),
        "origins": {"supplied": ["carrier", "product", "weight_rule", "path_factors", "preparations",
                                  "path_multiplication", "additive_recombination", "blocked_arm_deletion"],
                    "conditionally_computed": ["propagated_amplitudes", "summed_amplitude",
                                               "raw_weights", "interference_residual"],
                    "unsupported": ["derivation_from_native_IDT_base", "physical_preparability",
                                    "probability_readout", "physical_detector_law", "empirical_validation"]},
        "weight_meaning": "literal_supplied_raw_weight_not_probability_or_derived_detector_law",
        "counterfactual_meaning": "delete_one_arm_without_refitting_factors_or_renormalizing",
        "preflight_policy": "any_unsupported_mapping_prevents_all_execution_no_silent_skips",
        "budget": {"unit": "ordered_trace_step", "maximum": limits.max_cases, "checked": 0, "planned": planned},
        "unused_limits": ["coefficient_radius", "reference_radius", "max_copies"],
        "trace": [], "completed_preparations": [],
        "missing_bridges": ["native_base_to_supplied_model_and_protocol", "physical_preparation_and_path_factors",
                            "raw_weight_to_physical_probability_or_detector_readout"],
        "untested": ["universal_laws", "continuous_dynamics", "physical_time_or_lattice",
                     "QM", "SM", "gravity", "empirical_data"],
    }
    model: AmplitudeAlgebra | None = None
    if isinstance(bench.model, AmplitudeAlgebra):
        model = bench.model
        scope["model_origin"] = "explicit_supplied_algebra"
    else:
        resolved = resolve_source_algebra(bench.model)
        scope.update({"model_origin": "unbound_source_snapshot",
                      "source_missing_bridges": list(bench.model.missing_bridges),
                      "source_boundary": "snapshot_binding_not_source_execution_or_checked_proof"})
        if resolved is not None:
            model, key = resolved
            scope["model_origin"] = "exact_archived_source_specification_binding"
            scope["source_specification_sha256"] = key
    reason: dict[str, object] | None = None
    if bench.scenario != "two_path_v1":
        reason = {"kind": "scenario_mapping", "scenario": bench.scenario}
    elif model is None:
        reason = {"kind": "missing_exact_reviewed_source_binding"}
    if model is not None:
        scope["native_law"] = model.specification()
        if reason is None and model.carrier == "integer_scalar":
            for prep in bench.preparations:
                for field in AMPLITUDE_FIELDS:
                    amplitude = getattr(prep, field)
                    if amplitude[1] != 0:
                        reason = {"kind": "outside_integer_scalar_carrier", "preparation": prep.id,
                                  "field": field, "amplitude": list(amplitude)}
                        break
                if reason is not None:
                    break
    if reason is not None:
        scope["unsupported_reason"] = reason
        return (Check("two_path_execution_completion_only", "unsupported", 0, planned,
                      "complete_supplied_protocol_execution_only", ASSUMPTIONS, None),), scope
    assert model is not None
    trace: list[dict[str, object]] = []
    completed: list[dict[str, object]] = []
    for step in itertools.islice(_steps(model, bench.preparations), limits.max_cases):
        trace.append({"step": len(trace) + 1, **step})
        if step["operation"] == "subtract_blocked_weights":
            completed.append({"preparation": step["preparation"], "raw_weights": step["inputs"],
                              "interference_residual": step["output"]})
    complete = len(trace) == planned
    scope.update({"execution_status": "complete" if complete else "incomplete", "trace": trace,
                  "completed_preparations": completed,
                  "budget": {"unit": "ordered_trace_step", "maximum": limits.max_cases,
                             "checked": len(trace), "planned": planned}})
    check = Check("two_path_execution_completion_only", "no_counterexample_within_bounds" if complete else "inconclusive",
                  len(trace), planned, "complete_supplied_protocol_execution_only", ASSUMPTIONS, None)
    return (check,), scope
