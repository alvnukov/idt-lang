"""An ideal conditional null beside a published summary, never empirical acceptance."""

from __future__ import annotations

import re
from dataclasses import dataclass
from fractions import Fraction
from pathlib import Path

from theory_experiments.amplitude_algebra import (
    AmplitudeAlgebra,
    parse_amplitude_algebra,
    resolve_source_algebra,
)
from theory_experiments.primitive_screen import (
    Check,
    Limits,
    candidate_id,
    load_json,
    object_fields,
)
from theory_experiments.source_candidate import SourceCandidate, parse_source_candidate

ROOT = Path(__file__).resolve().parents[1]
EXPERIMENT = "sinha2010_hsps_kappa_v1"
BRIDGE = "fixed_path_quadratic_rate_v1"
DATA_PATH = "data/published_observations/sinha2010_hsps_kappa.json"
LEAN_PATH = "Proofs/QMClosure/PublishedSorkinNull.lean"
ASSUMPTIONS = (
    "unchanged_path_contributions_in_all_eight_contexts_including_empty",
    "additive_path_recombination",
    "supplied_quadratic_weight_extended_to_real_coordinates_not_derived_physics",
    "common_positive_gain_and_same_nonnegative_additive_background",
    "common_exposure_or_rate_convention",
    "nonzero_pair_interference_denominator",
    "physical_assignment_and_preparability_not_established",
    "apparatus_nuisance_bias_unmodeled_not_assumed_zero",
    "fixed_path_null_not_universal_actual_triple_slit_QM_prediction",
    "completion_only_not_empirical_acceptance_or_primitive_selection",
)


@dataclass(frozen=True)
class PublishedObservation:
    id: str
    experiment: str
    bridge: str
    model: AmplitudeAlgebra | SourceCandidate

    def __post_init__(self) -> None:
        for value in (self.id, self.experiment, self.bridge):
            candidate_id(value)
        if not isinstance(self.model, (AmplitudeAlgebra, SourceCandidate)):
            raise TypeError("published observation model requires amplitude_algebra or source_theory")

    def specification(self) -> dict[str, object]:
        return {"id": self.id, "family": "published_observation", "experiment": self.experiment,
                "bridge": self.bridge, "model": self.model.specification()}


def parse_published_observation(value: object) -> PublishedObservation:
    row = object_fields(value, {"id", "family", "experiment", "bridge", "model"})
    if row["family"] != "published_observation":
        raise ValueError("expected published_observation")
    raw = object_fields(row["model"])
    model: AmplitudeAlgebra | SourceCandidate
    if raw.get("family") == "amplitude_algebra":
        model = parse_amplitude_algebra(raw)
    elif raw.get("family") == "source_theory":
        model = parse_source_candidate(raw)
    else:
        raise ValueError("published observation model requires amplitude_algebra or source_theory; no nesting")
    return PublishedObservation(candidate_id(row["id"]), candidate_id(row["experiment"]),
                                candidate_id(row["bridge"]), model)


def predict_ideal_null(model: AmplitudeAlgebra) -> dict[str, object]:
    """No observation argument or registry access: eligibility and exact algebra only."""
    if model.weight_rule == "zero":
        return {"status": "unsupported", "reason": "zero_or_unestablished_denominator"}
    if model.weight_rule != "quadratic":
        return {"status": "unsupported", "reason": "missing_preparation_mapping"}
    if model.imaginary_weight < 0:
        return {"status": "unsupported", "reason": "missing_nonnegative_readout_bridge"}
    return {"status": "conditional_ideal_null", "ideal_epsilon": "0", "ideal_kappa": "0",
            "weight": "W(a,b)=a^2+eta*b^2", "eta": model.imaginary_weight,
            "domain": "assumed_real_quadratic_extension_of_supplied_integer_weight",
            "multiplication_parameter": "unused_no_path_propagation_or_preparation_is_inferred",
            "denominator": "conditional_nonzero_delta_not_established_from_published_summary",
            "artifact": LEAN_PATH,
            "artifact_relation": "reviewed_literal_weight_identity_not_formal_verification_of_Python",
            "proof_check": "not_run_by_this_evaluator"}


def _text(value: object) -> str:
    if not isinstance(value, str) or not value.strip() or len(value) > 2048:
        raise ValueError("expected bounded nonempty published-source text")
    return value


def _decimal(value: object) -> Fraction:
    if not isinstance(value, str) or not re.fullmatch(r"-?\d{1,8}\.\d{1,8}", value):
        raise ValueError("published values require bounded exact decimal strings")
    return Fraction(value)


def _summary(value: object, *, alternative: bool = False) -> dict[str, object]:
    fields = {"value", "quoted_uncertainty", "locator"} | ({"relation"} if alternative else set())
    row = object_fields(value, fields)
    _decimal(row["value"])
    if _decimal(row["quoted_uncertainty"]) <= 0:
        raise ValueError("quoted uncertainty must be strictly positive")
    _text(row["locator"])
    if alternative:
        _text(row["relation"])
    return row


def published_summary() -> dict[str, object]:
    """Trusted, fixed registry entry, not a candidate-selected file or observation."""
    row = object_fields(load_json(ROOT / DATA_PATH), {"schema", "id", "source", "observable", "regime",
        "primary", "alternative_same_summary", "uncertainty_interpretation", "limitations"})
    if row["schema"] != "idt-published-summary/1" or row["id"] != EXPERIMENT:
        raise ValueError("published summary schema/registry mismatch")
    source = object_fields(row["source"], {"title", "authors", "year", "doi", "abstract_url", "pdf_url",
                                         "pdf_sha256", "extraction"})
    if type(source["year"]) is not int or source["year"] != 2010:
        raise ValueError("invalid source year")
    for key, item in source.items():
        if key != "year":
            _text(item)
    if not re.fullmatch(r"[0-9a-f]{64}", _text(source["pdf_sha256"])):
        raise ValueError("invalid source PDF hash")
    observable = object_fields(row["observable"], {"name", "dimension", "epsilon", "delta", "kappa", "locator"})
    for item in observable.values():
        _text(item)
    if observable["name"] != "kappa" or observable["dimension"] != "dimensionless":
        raise ValueError("unsupported published observable or dimensions")
    _summary(row["primary"])
    _summary(row["alternative_same_summary"], alternative=True)
    _text(row["regime"])
    _text(row["uncertainty_interpretation"])
    limitations = row["limitations"]
    if not isinstance(limitations, list) or not 1 <= len(limitations) <= 16:
        raise ValueError("published limitations require a bounded nonempty array")
    for item in limitations:
        _text(item)
    return row


def compare_summary(ideal_kappa: Fraction, summary: object) -> dict[str, object]:
    """Exact descriptive subtraction/division, not a statistical test or likelihood."""
    row = _summary(summary)
    residual = _decimal(row["value"]) - ideal_kappa
    return {"measured_minus_ideal": str(residual),
            "residual_over_quoted_uncertainty": str(residual / _decimal(row["quoted_uncertainty"])),
            "interpretation": "descriptive_arithmetic_only_not_z_score_or_acceptance",
            "nuisance_bias": "unmodeled_not_zero",
            "apparatus_prediction": "not_available",
            "empirical_acceptance": "not_assessed"}


def evaluate_published_observation(candidate: PublishedObservation, limits: Limits
                                   ) -> tuple[tuple[Check, ...], dict[str, object]]:
    scope: dict[str, object] = {
        "scientific_status": "conditional_ideal_null_comparison", "candidate_verdict": "not_assessed",
        "execution_status": "unsupported", "experiment": candidate.experiment, "bridge": candidate.bridge,
        "budget": {"unit": "closed_form_descriptive_comparison", "planned": 1, "checked": 0,
                   "maximum": limits.max_cases},
        "unused_limits": ["coefficient_radius", "reference_radius", "max_copies"],
        "assumptions": list(ASSUMPTIONS),
        "missing_bridges": ["native_base_to_physical_preparation_and_path_assignment",
                            "apparatus_nuisance_model_and_raw_context_counts"],
        "comparison_policy": "no_fit_no_threshold_no_ranking_no_empirical_acceptance",
        "historical_source_policy": "frozen_runtime_policy_is_not_prospective_preregistration",
        "weight_meaning": "supplied_weight_not_normalized_probability",
    }
    reason: str | None = None
    model: AmplitudeAlgebra | None = None
    if candidate.experiment != EXPERIMENT:
        reason = "unknown_experiment"
    elif candidate.bridge != BRIDGE:
        reason = "missing_or_unknown_explicit_bridge"
    elif isinstance(candidate.model, AmplitudeAlgebra):
        model = candidate.model
        scope["model_origin"] = "explicit_supplied_algebra"
    else:
        resolved = resolve_source_algebra(candidate.model)
        scope["model_origin"] = "unbound_source_snapshot"
        scope["source_missing_bridges"] = list(candidate.model.missing_bridges)
        if resolved is None:
            reason = "missing_exact_reviewed_source_binding"
        else:
            model, key = resolved
            scope.update({"model_origin": "exact_archived_source_specification_binding",
                          "source_specification_sha256": key,
                          "source_boundary": "snapshot_binding_not_source_execution_or_checked_proof"})
    if model is not None:
        scope["supplied_model"] = model.specification()
        prediction = predict_ideal_null(model)
        scope["prediction"] = prediction
        if prediction["status"] == "unsupported":
            reason = _text(prediction["reason"])
    if reason is not None:
        scope["unsupported_reason"] = reason
        return (Check("published_summary_comparison_completion_only", "unsupported", 0, 1,
                      "complete_descriptive_comparison_only", ASSUMPTIONS, None),), scope
    assert model is not None
    # Prediction above has no access to measurement numbers; only now read the registry.
    data = published_summary()
    scope.update({"execution_status": "complete", "observation": data,
                  "comparison": compare_summary(Fraction(_text(prediction["ideal_kappa"])), data["primary"]),
                  "budget": {"unit": "closed_form_descriptive_comparison", "planned": 1, "checked": 1,
                             "maximum": limits.max_cases}})
    return (Check("published_summary_comparison_completion_only", "no_counterexample_within_bounds", 1, 1,
                  "complete_descriptive_comparison_only", ASSUMPTIONS, None),), scope
