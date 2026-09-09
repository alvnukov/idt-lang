"""Conditional exact QM/SM benchmarks, not a derivation or empirical fit."""

from __future__ import annotations

from collections import Counter
from dataclasses import dataclass
from fractions import Fraction as F
from typing import TypeAlias

from theory_experiments.primitive_screen import (
    Check,
    Limits,
    Trial,
    bounded_int,
    candidate_id,
    exact_fraction,
    object_fields,
    run_probe,
)

QM_IMPORTS = (
    "complex_amplitudes_and_linear_context_maps_are_supplied",
    "projective_measurements_and_tensor_composition_are_supplied",
    "normalized_power_of_amplitude_norm_is_the_candidate_readout",
    "reference_targets_use_standard_Born_QM_not_derived_from_primitives",
)
SM_IMPORTS = (
    "su3_su2_u1_Lie_algebra_is_supplied_global_group_quotient_is_unspecified",
    "left_handed_Weyl_fields_in_singlet_or_fundamental_representations",
    "Q_equals_T3_plus_Y_and_one_complex_scalar_Higgs_doublet_are_supplied",
    "anomaly_formulas_are_imported_QFT_consistency_conditions",
    "content_target_is_minimal_three_generation_SM_not_all_allowed_extensions",
)
COMMON_GAPS = (
    "derivation_from_lower_primitives", "experimental_data_and_uncertainties",
    "detector_actualization", "gravity", "universal_formal_proof",
)


@dataclass(frozen=True)
class QuantumReadout:
    id: str
    norm_power: int

    def __post_init__(self) -> None:
        candidate_id(self.id)
        bounded_int(self.norm_power, 1, 4)

    def specification(self) -> dict[str, object]:
        return {"id": self.id, "family": "qm_readout", "norm_power": self.norm_power}


@dataclass(frozen=True)
class WeylField:
    label: str
    color: int
    weak: int
    hypercharge: F
    copies: int

    def __post_init__(self) -> None:
        candidate_id(self.label)
        if type(self.color) is not int or self.color not in (1, 3, -3):
            raise ValueError("color supports only 1, 3, -3 (antifundamental)")
        bounded_int(self.weak, 1, 2)
        bounded_int(self.copies, 1, 8)
        if not isinstance(self.hypercharge, F):
            raise TypeError("hypercharge must be an exact Fraction")
        exact_fraction(str(self.hypercharge))

    def specification(self) -> dict[str, object]:
        return {"label": self.label, "color": self.color, "weak": self.weak,
                "hypercharge": str(self.hypercharge), "copies": self.copies}


@dataclass(frozen=True)
class ChiralSpectrum:
    id: str
    fields: tuple[WeylField, ...]
    higgs_hypercharge: F

    def __post_init__(self) -> None:
        candidate_id(self.id)
        bounded_int(len(self.fields), 1, 16)
        if len({field.label for field in self.fields}) != len(self.fields):
            raise ValueError("field labels must be unique")
        if not isinstance(self.higgs_hypercharge, F):
            raise TypeError("Higgs hypercharge must be an exact Fraction")
        exact_fraction(str(self.higgs_hypercharge))

    def specification(self) -> dict[str, object]:
        return {"id": self.id, "family": "sm_chiral", "fields": [
            field.specification() for field in self.fields],
            "higgs_hypercharge": str(self.higgs_hypercharge)}


PhysicsCandidate: TypeAlias = QuantumReadout | ChiralSpectrum


def parse_physics(value: object) -> PhysicsCandidate:
    row = object_fields(value)
    if row.get("family") == "qm_readout":
        object_fields(row, {"id", "family", "norm_power"})
        return QuantumReadout(candidate_id(row["id"]), bounded_int(row["norm_power"], 1, 4))
    if row.get("family") != "sm_chiral":
        raise ValueError("unsupported physics family")
    object_fields(row, {"id", "family", "fields", "higgs_hypercharge"})
    fields = row["fields"]
    if not isinstance(fields, list) or not 1 <= len(fields) <= 16:
        raise ValueError("fields must be a list of 1 to 16 Weyl multiplets")
    parsed: list[WeylField] = []
    for item in fields:
        field = object_fields(item, {"label", "color", "weak", "hypercharge", "copies"})
        parsed.append(WeylField(candidate_id(field["label"]),
                                bounded_int(field["color"], -3, 3),
                                bounded_int(field["weak"], 1, 2),
                                exact_fraction(field["hypercharge"]),
                                bounded_int(field["copies"], 1, 8)))
    return ChiralSpectrum(candidate_id(row["id"]), tuple(parsed),
                          exact_fraction(row["higgs_hypercharge"]))


def physics_controls() -> dict[str, PhysicsCandidate]:
    # Candidate inputs, separate from the target multiset in evaluate_sm.
    def spectrum(name: str, copies: int, electron_y: F) -> ChiralSpectrum:
        return ChiralSpectrum(name, (
            WeylField("q", 3, 2, F(1, 6), copies),
            WeylField("uc", -3, 1, F(-2, 3), copies),
            WeylField("dc", -3, 1, F(1, 3), copies),
            WeylField("l", 1, 2, F(-1, 2), copies),
            WeylField("ec", 1, 1, electron_y, copies),
        ), F(1, 2))
    return {"qm_born": QuantumReadout("qm_born", 1),
            "qm_fourth": QuantumReadout("qm_fourth", 2),
            "sm_reference": spectrum("sm_reference", 3, F(1)),
            "sm_bad_charge": spectrum("sm_bad_charge", 3, F(2)),
            "sm_one_generation": spectrum("sm_one_generation", 1, F(1))}


Amplitude: TypeAlias = tuple[F, F]  # Gaussian rational (real, imaginary).
RealMatrix: TypeAlias = tuple[tuple[F, F], tuple[F, F]]


def probabilities(amplitudes: tuple[Amplitude, ...], power: int) -> tuple[F, ...]:
    weights = tuple((real * real + imag * imag) ** power for real, imag in amplitudes)
    total = sum(weights, F())
    if total == 0:
        raise ValueError("zero vector has no normalized readout")
    return tuple(weight / total for weight in weights)


def real_probabilities(amplitudes: tuple[F, ...], power: int) -> tuple[F, ...]:
    return probabilities(tuple((x, F()) for x in amplitudes), power)


def correlation(left: RealMatrix, right: RealMatrix, power: int) -> F:
    # Apply A tensor B to the unnormalized singlet |01> - |10>.
    amplitudes = tuple(left[a][0] * right[b][1] - left[a][1] * right[b][0]
                       for a in range(2) for b in range(2))
    p = real_probabilities(amplitudes, power)
    return p[0] - p[1] - p[2] + p[3]


def evaluate_qm(candidate: QuantumReadout, limits: Limits) -> tuple[Check, ...]:
    power = candidate.norm_power
    identity: RealMatrix = ((F(1), F(0)), (F(0), F(1)))
    # H is a common scalar times a unitary. Normalization removes that scalar.
    hadamard: RealMatrix = ((F(1), F(1)), (F(1), F(-1)))
    plus: RealMatrix = ((F(4, 5), F(3, 5)), (F(-3, 5), F(4, 5)))
    minus: RealMatrix = ((F(4, 5), F(-3, 5)), (F(3, 5), F(4, 5)))
    phases = ((F(1), F(0)), (F(0), F(1)), (F(-1), F(0)),
              (F(0), F(-1)), (F(3, 5), F(4, 5)))
    interference = tuple(Trial({"phase": [str(r), str(i)],
                               "reference_p0": str((1 + r) / 2)},
                              probabilities(((1 + r, i), (1 - r, -i)), power)[0]
                              - (1 + r) / 2) for r, i in phases)
    before = real_probabilities((F(5), F(0), F(3), F(4)), power)
    rotation: RealMatrix = ((F(3, 5), F(4, 5)), (F(-4, 5), F(3, 5)))
    state = ((F(5), F(0)), (F(3), F(4)))
    rotated = tuple(sum((rotation[b][j] * state[a][j] for j in range(2)), F())
                    for a in range(2) for b in range(2))
    after = real_probabilities(rotated, power)
    contexts = ((identity, plus), (identity, minus), (hadamard, plus), (hadamard, minus))
    correlations = tuple(correlation(a, b, power) for a, b in contexts)
    targets = (F(-7, 25), F(-7, 25), F(-24, 25), F(24, 25))
    chsh = correlations[0] + correlations[1] + correlations[2] - correlations[3]
    probes = (
        ("qm_born_reference", (Trial({"state": ["3", "4"], "reference_p0": "9/25"},
                                    real_probabilities((F(3), F(4)), power)[0] - F(9, 25)),), "=0"),
        ("qm_phase_interference", interference, "=0"),
        ("qm_projective_repeatability", tuple(Trial({"selected": i},
             real_probabilities(tuple(F(j == i) for j in range(2)), power)[i] - 1)
             for i in range(2)), "=0"),
        ("qm_local_no_signalling", (Trial({"state": ["5", "0", "3", "4"],
             "bob_rotation": [[str(x) for x in row] for row in rotation],
             "alice_p0_before": str(before[0] + before[1]),
             "alice_p0_after": str(after[0] + after[1])},
             after[0] + after[1] - before[0] - before[1]),), "=0"),
        ("qm_singlet_correlations", tuple(Trial({"context": i, "reference_E": str(target)},
             actual - target) for i, (actual, target) in enumerate(zip(correlations, targets))), "=0"),
        ("qm_tsirelson_bound", (Trial({"S": str(chsh), "correlations": list(map(str, correlations))},
                                     8 - chsh * chsh),), ">=0"),
    )
    return tuple(run_probe(name, trials, len(trials), ">=0" if requirement == ">=0" else "=0",
                           QM_IMPORTS, limits) for name, trials, requirement in probes)


def evaluate_sm(candidate: ChiralSpectrum, limits: Limits) -> tuple[Check, ...]:
    totals = {key: F() for key in ("su3_cubic", "su3_squared_y", "su2_squared_y",
                                  "y_cubic", "mixed_gravitational_y", "witten_doublets")}
    actual: Counter[tuple[int, int, F]] = Counter()
    for field in candidate.fields:
        c, w, y, n = field.color, field.weak, field.hypercharge, field.copies
        dimension = abs(c) * w * n
        actual[c, w, y] += n
        if abs(c) == 3:
            totals["su3_cubic"] += (1 if c > 0 else -1) * w * n
            totals["su3_squared_y"] += w * y * n
        if w == 2:
            totals["su2_squared_y"] += abs(c) * y * n
            totals["witten_doublets"] += abs(c) * n
        totals["y_cubic"] += dimension * y ** 3
        totals["mixed_gravitational_y"] += dimension * y
    # Dynkin factors use 2 T(fundamental)=1; only the common nonzero factor is omitted.
    checks = [run_probe("sm_" + key, (Trial({"coefficient": str(value)},
                value % 2 if key == "witten_doublets" else value),), 1, "=0", SM_IMPORTS, limits)
              for key, value in totals.items()]
    target = Counter({(3, 2, F(1, 6)): 3, (-3, 1, F(-2, 3)): 3,
                      (-3, 1, F(1, 3)): 3, (1, 2, F(-1, 2)): 3, (1, 1, F(1)): 3})
    signatures = sorted(set(actual) | set(target))
    trials = tuple(Trial({"color": c, "weak": w, "Y": str(y),
                          "candidate_copies": actual[c, w, y], "target_copies": target[c, w, y]},
                         F(actual[c, w, y] - target[c, w, y])) for c, w, y in signatures)
    checks.append(run_probe("sm_minimal_multiplet_content", trials, len(trials), "=0", SM_IMPORTS, limits))
    checks.append(run_probe("sm_neutral_higgs_lower_component", (Trial({
        "higgs_Y": str(candidate.higgs_hypercharge), "assumed_vev_component_T3": "-1/2"},
        candidate.higgs_hypercharge - F(1, 2)),), 1, "=0", SM_IMPORTS, limits))
    return tuple(checks)


def scope(candidate: PhysicsCandidate) -> dict[str, object]:
    if isinstance(candidate, QuantumReadout):
        return {"imports": list(QM_IMPORTS), "untested": list(COMMON_GAPS) + [
            "all_states_and_settings", "general_POVMs", "continuous_dynamics",
            "complex_Hilbert_space_derivation", "hbar_scale", "standard_model"]}
    return {"imports": list(SM_IMPORTS), "untested": list(COMMON_GAPS) + [
        "mass_spectrum", "Yukawa_couplings_and_mixing", "neutrino_mass_mechanism",
        "cross_sections_and_decays", "renormalization", "higher_representations",
        "all_global_anomalies", "global_gauge_group", "quantum_mechanics_derivation"],
        "derived_electric_charges": [{"field": field.label, "copies": field.copies,
             "color_dimension": abs(field.color), "charges": [str(field.hypercharge + t3)
             for t3 in ((F(1, 2), F(-1, 2)) if field.weak == 2 else (F(0),))]}
             for field in candidate.fields]}
