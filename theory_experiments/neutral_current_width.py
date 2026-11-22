"""Conditional invisible Z-width readout for a supplied Dirac left neutral current."""

from __future__ import annotations

import hashlib
import json
import re
from dataclasses import dataclass
from fractions import Fraction
from pathlib import Path

from theory_experiments import primitive_screen as primitive
from theory_experiments.primitive_screen import Check, Limits, candidate_id, object_fields

ROOT = Path(__file__).resolve().parents[1]
LOADED_SOURCE_SHA256 = hashlib.sha256(Path(__file__).read_bytes()).hexdigest()
DATA_PATH = "data/published_observations/z_invisible_width_v1.json"
# Pin exact curated bytes, not a hash sampled at import time.
DATA_SHA256 = "e45139ef489067182eea77faeab03f1bb29db3a58b5db4e4eab635e22b068e97"
MAX_SPECIES = 12
MASS_REGIMES = ("all_negligible", "threshold_or_unknown")
BRIDGES = ("standard_invisible_left_current_only", "unmapped")
ASSUMPTIONS = (
    "supplied_light_Dirac_mass_eigenstates_and_calibrated_dimensionless_left_Z_current",
    "unit_diagonal_coupling_is_one_standard_neutrino_width_not_one_arbitrary_slot",
    "common_Z_pole_line_shape_and_standard_charged_lepton_normalization",
    "all_species_negligible_mass_for_Z_decay_and_detector_stable_invisible",
    "all_ordered_particle_antiparticle_channels_distinct_no_extra_invisible_width",
    "no_right_current_threshold_correction_or_visible_new_physics",
)
_COMPONENT = re.compile(r"-?[0-9]{1,9}(?:/[1-9][0-9]{0,8})?")
Component = tuple[Fraction, Fraction]
Matrix = tuple[tuple[Component, ...], ...]


def _component(value: object) -> Fraction:
    # Nine digits bounds both parser work and denominator growth of the full trace.
    if type(value) is not str or len(value) > 20 or not _COMPONENT.fullmatch(value):
        raise ValueError("current entries require bounded exact rational strings")
    return Fraction(value)


def _pair(value: object) -> Component:
    if type(value) is not list or len(value) != 2:
        raise ValueError("current entries must be [real-string, imaginary-string]")
    return _component(value[0]), _component(value[1])


@dataclass(frozen=True)
class NeutralCurrentWidth:
    id: str
    species: tuple[str, ...]
    mass_regime: str
    bridge: str
    left_current_matrix: Matrix

    def __post_init__(self) -> None:
        candidate_id(self.id)
        if type(self.species) is not tuple or not 1 <= len(self.species) <= MAX_SPECIES:
            raise ValueError("expected 1..12 supplied Dirac species")
        for label in self.species:
            candidate_id(label)
        if len(set(self.species)) != len(self.species):
            raise ValueError("duplicate species label")
        if self.mass_regime not in MASS_REGIMES or self.bridge not in BRIDGES:
            raise ValueError("unknown mass regime or bridge flag")
        n = len(self.species)
        matrix = self.left_current_matrix
        if type(matrix) is not tuple or len(matrix) != n:
            raise ValueError("matrix height must equal species count")
        for row in matrix:
            if type(row) is not tuple or len(row) != n:
                raise ValueError("matrix width must equal species count")
            for z in row:
                if (type(z) is not tuple or len(z) != 2 or
                    any(type(x) is not Fraction or abs(x.numerator) >= 10**9 or
                        x.denominator >= 10**9 for x in z)):
                    raise ValueError("invalid bounded rational pair")
        for i in range(n):
            for j in range(i, n):
                real, imag = matrix[i][j]
                if matrix[j][i] != (real, -imag):
                    raise ValueError("left-current matrix must be Hermitian")

    def specification(self) -> dict[str, object]:
        return {"id": self.id, "family": "neutral_current_width", "species": list(self.species),
                "mass_regime": self.mass_regime, "bridge": self.bridge,
                "left_current_matrix": [[[str(r), str(i)] for r, i in row]
                                        for row in self.left_current_matrix]}


def parse_neutral_current_width(value: object) -> NeutralCurrentWidth:
    if type(value) is not dict or len(value) != 6:
        raise ValueError("expected exactly six neutral-current candidate fields")
    row = object_fields(value, {"id", "family", "species", "mass_regime", "bridge", "left_current_matrix"})
    if row["family"] != "neutral_current_width":
        raise ValueError("expected neutral_current_width")
    labels = row["species"]
    if type(labels) is not list or not 1 <= len(labels) <= MAX_SPECIES:
        raise ValueError("expected 1..12 supplied Dirac species")
    species = tuple(candidate_id(label) for label in labels)
    matrix = row["left_current_matrix"]
    if type(matrix) is not list or len(matrix) != len(species):
        raise ValueError("matrix height must equal species count")
    for line in matrix:
        if type(line) is not list or len(line) != len(species):
            raise ValueError("matrix width must equal species count")
    return NeutralCurrentWidth(candidate_id(row["id"]), species, candidate_id(row["mass_regime"]),
                              candidate_id(row["bridge"]), tuple(tuple(_pair(z) for z in line)
                                                                for line in matrix))


def predict_neutral_current_width(candidate: NeutralCurrentWidth, limits: Limits) -> dict[str, object]:
    """Frobenius norm squared: the rate sums over distinguishable ordered final states."""
    n = len(candidate.species)
    planned = n * n
    budget = {"unit": "ordered_Dirac_particle_antiparticle_channel", "planned": planned,
              "maximum": limits.max_cases, "checked": 0}
    if candidate.mass_regime != "all_negligible":
        return {"status": "unsupported", "reason": "masses_or_threshold_factors_not_mapped", "budget": budget}
    if candidate.bridge != "standard_invisible_left_current_only":
        return {"status": "unsupported", "reason": "neutral_current_bridge_unmapped", "budget": budget}
    if limits.max_cases < planned:
        return {"status": "inconclusive", "reason": "full_channel_budget_required", "budget": budget}
    channels = []
    total = Fraction()
    for i, row in enumerate(candidate.left_current_matrix):
        for j, (real, imag) in enumerate(row):
            weight = real * real + imag * imag
            total += weight
            channels.append({"particle": candidate.species[i], "antiparticle": candidate.species[j],
                             "squared_coupling": str(weight)})
    budget["checked"] = planned
    return {"status": "complete", "formula": "sum_ij_abs_Cij_squared", "effective_species": str(total),
            "ordered_channels": channels, "budget": budget}


def _pinned_receipt_bytes() -> bytes:
    with (ROOT / DATA_PATH).open("rb") as f:
        raw = f.read(65537)
    if len(raw) > 65536 or hashlib.sha256(raw).hexdigest() != DATA_SHA256:
        raise ValueError("neutral-current published receipt digest mismatch")
    return raw


def _assert_code_unchanged() -> None:
    for path, loaded in ((Path(__file__), LOADED_SOURCE_SHA256),
                         (Path(primitive.__file__), primitive.LOADED_SOURCE_SHA256)):
        if hashlib.sha256(path.read_bytes()).hexdigest() != loaded:
            raise ValueError(f"neutral-current source changed since import: {path.name}")


def assert_loaded_sources() -> None:
    """Fail closed for changed adapter, directly used helper, or frozen data bytes."""
    _assert_code_unchanged()
    _pinned_receipt_bytes()


def _comparison(effective_species: Fraction) -> dict[str, object]:
    # Decode and compare the same pinned bytes. Published decimal spelling is part of the evidence.
    receipt = json.loads(_pinned_receipt_bytes(), parse_float=str, parse_int=str,
                         parse_constant=primitive.reject_nonexact_number,
                         object_pairs_hook=primitive.reject_duplicate_keys)
    measured = receipt["lep_updated"]["n_eff"]
    residual = Fraction(measured["value"]) - effective_species
    gamma_l = receipt["lep_original"]["gamma_lepton_mev"]
    r_nu = receipt["lep_updated"]["r_nu"]
    one_species_mev = Fraction(gamma_l["value"]) * Fraction(r_nu["value"])
    predicted_mev = effective_species * one_species_mev
    atlas = receipt["atlas"]["gamma_inv_mev"]
    return {"source_path": DATA_PATH, "source_sha256": DATA_SHA256,
            "lep_updated": {"printed_effective_species": measured["value"],
                            "printed_quoted_uncertainty": measured["error"],
                            "measured_minus_predicted": str(residual),
                            "residual_over_quoted_uncertainty": str(residual / Fraction(measured["error"])),
                            "interpretation": "descriptive_only_not_significance_or_acceptance"},
            "lep_original": "same_LEP_sample_not_an_independent_measurement_not_combined",
            "atlas": {"reported_invisible_width_mev": atlas,
                      "status": "secondary_descriptive_method_only",
                      "calibration": {"lep_original_gamma_lepton_mev": gamma_l, "lep_updated_r_nu": r_nu,
                                      "formula": "N_eff * Gamma_lepton_original_LEP * r_nu_updated_SM",
                                      "one_standard_species_mev": str(one_species_mev)},
                      "predicted_invisible_width_mev": str(predicted_mev),
                      "measured_minus_predicted_mev": str(Fraction(atlas["value"]) - predicted_mev),
                      "interpretation": "hybrid_external_calibration_uncertainties_not_propagated_"
                                        "no_independent_likelihood_no_combined_significance"},
            "candidate_ranking": "not_attempted"}


def evaluate_neutral_current_width(candidate: NeutralCurrentWidth, limits: Limits
                                   ) -> tuple[tuple[Check, ...], dict[str, object]]:
    _assert_code_unchanged()
    prediction = predict_neutral_current_width(candidate, limits)
    status = prediction["status"]
    scope = {"scientific_status": "conditional_calibrated_neutral_current_width",
             "execution_status": status, "prediction": prediction, "budget": prediction["budget"],
             "candidate_verdict": "not_assessed", "proof_status": "not_attempted",
             "empirical_status": "not_tested", "assumptions": list(ASSUMPTIONS),
             "model_origin": "supplied_current_and_mass_basis_not_inferred_from_slots_or_primitives",
             "comparison_policy": "no_fit_no_threshold_no_ranking_no_empirical_acceptance",
             "unused_limits": ["coefficient_radius", "reference_radius", "max_copies"]}
    if status == "complete":
        scope["comparison"] = _comparison(Fraction(prediction["effective_species"]))
    elif status == "unsupported":
        scope["unsupported_reason"] = prediction["reason"]
    budget = prediction["budget"]
    check = Check("neutral_current_width_comparison_completion_only",
                  "no_counterexample_within_bounds" if status == "complete" else status,
                  budget["checked"], budget["planned"], "complete_descriptive_comparison_only",
                  ASSUMPTIONS, None)
    return (check,), scope
