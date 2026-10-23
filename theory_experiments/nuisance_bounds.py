"""Conditional scalar epsilon bounds, not apparatus inference or model selection.

ehat is the all-cycle recorded estimator. mu is its expectation under a supplied
ensemble using the identical acquisition/reduction recipe; q is ideal epsilon.
The supplied bounds must hold simultaneously. Their truth, ensemble definition,
complete error decomposition and physical bridge are external assumptions.
"""

from __future__ import annotations

import hashlib
import re
from dataclasses import dataclass
from fractions import Fraction
from pathlib import Path

LOADED_SOURCE_SHA256 = hashlib.sha256(Path(__file__).read_bytes()).hexdigest()


def assert_loaded_source_unchanged() -> None:
    """Detect a cached dependency imported before its on-disk source changed."""
    if hashlib.sha256(Path(__file__).read_bytes()).hexdigest() != LOADED_SOURCE_SHA256:
        raise ValueError("nuisance bounds source changed since import; restart interpreter")


@dataclass(frozen=True)
class ScalarInterval:
    lower: Fraction
    upper: Fraction

    def __post_init__(self) -> None:
        if type(self.lower) is not Fraction or type(self.upper) is not Fraction:
            raise ValueError("interval endpoints must be exact Fraction values, not floats")
        if self.lower > self.upper:
            raise ValueError("interval endpoints must be ordered")

    @property
    def contains_zero(self) -> bool:
        return self.lower <= 0 <= self.upper

    def as_report(self) -> dict[str, str]:
        return {"lower_exact": str(self.lower), "upper_exact": str(self.upper)}


@dataclass(frozen=True)
class ReplayTarget:
    run_id: str
    raw_sha256: str
    recipe_sha256: str

    def __post_init__(self) -> None:
        if not isinstance(self.run_id, str) or not self.run_id.strip():
            raise ValueError("target requires a nonempty run id")
        for digest in (self.raw_sha256, self.recipe_sha256):
            if not isinstance(digest, str) or re.fullmatch(r"[0-9a-f]{64}", digest) is None:
                raise ValueError("target requires lowercase SHA256 digests")

    def as_report(self) -> dict[str, str]:
        return {"run_id": self.run_id, "raw_sha256": self.raw_sha256,
                "recipe_sha256": self.recipe_sha256}


@dataclass(frozen=True)
class SuppliedBound:
    interval: ScalarInterval
    quantity: str
    sign_convention: str
    target: ReplayTarget
    source_ref: str
    assumptions: tuple[str, ...]
    evidence_kind: str
    depends_on_tested_null: bool
    observable: str
    unit: str

    def __post_init__(self) -> None:
        if not isinstance(self.interval, ScalarInterval) or not isinstance(self.target, ReplayTarget):
            raise TypeError("bound requires a typed exact interval and replay target")
        if not isinstance(self.source_ref, str) or not self.source_ref.strip():
            raise ValueError("bound requires a nonempty source reference")
        if (type(self.assumptions) is not tuple or not self.assumptions or
                any(not isinstance(a, str) or not a.strip() for a in self.assumptions)):
            raise ValueError("bound requires a nonempty immutable tuple of explicit assumptions")
        if not isinstance(self.evidence_kind, str) or not self.evidence_kind.strip():
            raise ValueError("bound requires an evidence kind")
        if type(self.depends_on_tested_null) is not bool:
            raise ValueError("depends_on_tested_null must be explicit boolean metadata")

    def as_report(self) -> dict[str, object]:
        return {"interval_volt": self.interval.as_report(), "quantity": self.quantity,
                "sign_convention": self.sign_convention, "target": self.target.as_report(),
                "source_ref": self.source_ref, "assumptions": self.assumptions,
                "evidence_kind": self.evidence_kind,
                "depends_on_tested_null": self.depends_on_tested_null,
                "observable": self.observable, "unit": self.unit}


@dataclass(frozen=True)
class NuisanceBounds:
    sampling: SuppliedBound | None = None
    bias: SuppliedBound | None = None


@dataclass(frozen=True)
class EpsilonAssessment:
    status: str
    ehat: Fraction
    target: ReplayTarget
    bounds: NuisanceBounds
    missing_bounds: tuple[str, ...]
    unsupported_evidence: tuple[str, ...]
    q_interval: ScalarInterval | None = None

    def as_report(self) -> dict[str, object]:
        return {"status": self.status, "candidate_verdict": "not_assessed",
                "recorded_mean_cycle_epsilon_volt_exact": str(self.ehat),
                "target": self.target.as_report(), "missing_bounds": self.missing_bounds,
                "unsupported_evidence": self.unsupported_evidence,
                "sampling_bound": self.bounds.sampling.as_report() if self.bounds.sampling else None,
                "bias_bound": self.bounds.bias.as_report() if self.bounds.bias else None,
                "ideal_epsilon_enclosure_volt": self.q_interval.as_report() if self.q_interval else None,
                "definitions": {"ehat": "exact_mean_cycle_epsilon_all_recorded_cycles",
                                "mu": "expectation_of_identical_acquisition_and_reduction_recipe_under_supplied_ensemble",
                                "q": "corresponding_ideal_fixed_path_epsilon",
                                "s": "ehat_minus_mu", "b": "mu_minus_q"},
                "external_assumptions": (
                    "supplied_ensemble_and_expectation_are_well_defined",
                    "both_signed_bounds_are_simultaneously_valid_for_this_estimator",
                    "sampling_plus_bias_is_the_complete_error_decomposition",
                    "physical_bridge_to_ideal_fixed_path_epsilon_is_valid"),
                "scope": "declared_provenance_checks_and_conditional_scalar_transfer_only_not_bound_certification",
                "zero_retained_meaning": "not_acceptance_or_model_feasibility",
                "zero_excluded_meaning": "joint_null_bridge_and_bounds_inconsistent_not_primitive_rejection",
                "kappa_propagation": "not_performed"}


def transfer(ehat: Fraction, sampling: ScalarInterval, bias: ScalarInterval) -> ScalarInterval:
    """Exact enclosure from s=ehat-mu and b=mu-q; no stochastic assumptions."""
    if (type(ehat) is not Fraction or not isinstance(sampling, ScalarInterval) or
            not isinstance(bias, ScalarInterval)):
        raise ValueError("transfer requires exact Fraction ehat and typed intervals")
    return ScalarInterval(ehat - sampling.upper - bias.upper,
                          ehat - sampling.lower - bias.lower)


def assess_epsilon(ehat: Fraction, target: ReplayTarget,
                   bounds: NuisanceBounds | None = None) -> EpsilonAssessment:
    """Validate binding before eligibility; never substitute zero for a missing bound.

    Same-data provenance is NOT automatically circular. Only the explicit null
    dependence flag rejects null-derived calibration. No independence is tested.
    Contract errors raise first; unsupported supplied evidence takes status
    precedence over a missing slot, whose name remains in missing_bounds.
    """
    if bounds is None:
        bounds = NuisanceBounds()
    if type(ehat) is not Fraction or not isinstance(target, ReplayTarget) or not isinstance(bounds, NuisanceBounds):
        raise ValueError("assessment requires exact ehat and typed target/bounds")
    missing: list[str] = []
    unsupported: list[str] = []
    circular = False
    for name, bound, quantity, sign in (
            ("sampling", bounds.sampling, "sampling_measurement_error", "recorded_minus_expected"),
            ("bias", bounds.bias, "apparatus_context_switch_bias", "expected_minus_ideal")):
        if bound is None:
            missing.append(name)
            continue
        if not isinstance(bound, SuppliedBound):
            raise TypeError(f"{name} bound must be a SuppliedBound or None")
        if (bound.observable != "mean_cycle_epsilon" or bound.unit != "volt" or
                bound.quantity != quantity or bound.sign_convention != sign or bound.target != target):
            raise ValueError(f"{name} observable/quantity/sign/unit/run/raw/recipe contract mismatch")
        if bound.depends_on_tested_null:
            circular = True
            unsupported.append(f"{name}:unsupported_circular_null_calibration")
        elif bound.evidence_kind != "supplied_deterministic_bound":
            unsupported.append(f"{name}:unsupported_evidence_kind:{bound.evidence_kind}")
    enclosure = None
    if unsupported:
        status = "unsupported_circular_null_calibration" if circular else "unsupported_evidence_kind"
    elif missing:
        status = "inconclusive_missing_bounds"
    else:
        assert bounds.sampling is not None and bounds.bias is not None
        enclosure = transfer(ehat, bounds.sampling.interval, bounds.bias.interval)
        status = ("zero_not_excluded_by_supplied_bounds" if enclosure.contains_zero else
                  "conditional_joint_null_bridge_bounds_inconsistent")
    return EpsilonAssessment(status, ehat, target, bounds, tuple(missing), tuple(unsupported), enclosure)
