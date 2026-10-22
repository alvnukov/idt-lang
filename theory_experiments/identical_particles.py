"""Exact identities of a supplied finite two-particle tensor, not a native prediction."""

from __future__ import annotations

from collections.abc import Iterable
from dataclasses import dataclass
from fractions import Fraction
from typing import Literal, TypeAlias

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

Amplitude: TypeAlias = tuple[Fraction, Fraction]
Mode: TypeAlias = tuple[str, str]
Statistics: TypeAlias = Literal["fermion", "boson"]
ASSUMPTIONS = (
    "supplied_fixture_not_prediction_from_IDT_primitives",
    "supplied_orthonormal_complete_modes_including_internal_degrees_of_freedom",
    "labels_do_not_certify_physical_mode_completeness_or_orthogonality",
    "supplied_complex_rational_two_particle_amplitudes_and_declared_statistics",
    "homogeneous_amplitude_identities_do_not_require_normalization",
    "exchange_uses_transpose_not_conjugate_transpose",
)


@dataclass(frozen=True)
class IdenticalPairAmplitudes:
    id: str
    statistics: Statistics
    modes: tuple[Mode, ...]
    amplitudes: tuple[tuple[Amplitude, ...], ...]
    origin: Literal["supplied_fixture"] = "supplied_fixture"

    def __post_init__(self) -> None:
        candidate_id(self.id)
        if self.statistics not in ("fermion", "boson") or self.origin != "supplied_fixture":
            raise ValueError("only declared fermion/boson supplied fixtures are supported")
        size = bounded_int(len(self.modes), 1, 4)
        for mode in self.modes:
            if len(mode) != 2:
                raise ValueError("complete mode requires orbital and internal labels")
            for label in mode:
                candidate_id(label)
        if len(set(self.modes)) != size:
            raise ValueError("duplicate complete mode")
        if len(self.amplitudes) != size or any(len(row) != size for row in self.amplitudes):
            raise ValueError("amplitudes must be an N by N matrix matching modes")
        for row in self.amplitudes:
            for amplitude in row:
                if len(amplitude) != 2 or any(not isinstance(part, Fraction) for part in amplitude):
                    raise ValueError("amplitudes require exact rational real and imaginary parts")
                for part in amplitude:
                    exact_fraction(str(part))

    def specification(self) -> dict[str, object]:
        return {"id": self.id, "family": "identical_pair_amplitudes", "origin": self.origin,
                "statistics": self.statistics,
                "modes": [{"orbital": orbital, "internal": internal} for orbital, internal in self.modes],
                "amplitudes": [[[str(re), str(im)] for re, im in row] for row in self.amplitudes]}


def parse_identical_pair(value: object) -> IdenticalPairAmplitudes:
    row = object_fields(value, {"id", "family", "origin", "statistics", "modes", "amplitudes"})
    if row["family"] != "identical_pair_amplitudes" or row["origin"] != "supplied_fixture":
        raise ValueError("expected identical_pair_amplitudes with supplied_fixture origin")
    statistics = row["statistics"]
    if statistics not in ("fermion", "boson"):
        raise ValueError("statistics must be fermion or boson")
    modes, matrix = row["modes"], row["amplitudes"]
    if not isinstance(modes, list) or not 1 <= len(modes) <= 4:
        raise ValueError("modes must contain 1 to 4 complete modes")
    parsed_modes: list[Mode] = []
    for mode in modes:
        fields = object_fields(mode, {"orbital", "internal"})
        parsed_modes.append((candidate_id(fields["orbital"]), candidate_id(fields["internal"])))
    if not isinstance(matrix, list) or len(matrix) != len(modes):
        raise ValueError("amplitudes must match the mode dimension")
    parsed_rows: list[tuple[Amplitude, ...]] = []
    for values in matrix:
        if not isinstance(values, list) or len(values) != len(modes):
            raise ValueError("amplitudes must be square")
        entries: list[Amplitude] = []
        for amplitude in values:
            if not isinstance(amplitude, list) or len(amplitude) != 2:
                raise ValueError("each amplitude must be [real, imaginary] rational strings")
            entries.append((exact_fraction(amplitude[0]), exact_fraction(amplitude[1])))
        parsed_rows.append(tuple(entries))
    return IdenticalPairAmplitudes(candidate_id(row["id"]),
        "fermion" if statistics == "fermion" else "boson", tuple(parsed_modes), tuple(parsed_rows))


def _residuals(model: IdenticalPairAmplitudes, *, diagonal: bool) -> Iterable[Trial]:
    for i in range(len(model.modes)):
        for j in (range(i, i + 1) if diagonal else range(i, len(model.modes))):
            a, b = model.amplitudes[i][j], model.amplitudes[j][i]
            sign = 1 if model.statistics == "fermion" else -1
            residual = a if diagonal else (a[0] + sign * b[0], a[1] + sign * b[1])
            for component, actual in zip(("real", "imaginary"), residual):
                yield Trial({"i": i, "j": j, "component": component,
                             "complex_residual": [str(part) for part in residual]}, actual)


def evaluate_identical_pair(model: IdenticalPairAmplitudes,
                            limits: Limits) -> tuple[tuple[Check, ...], dict[str, object]]:
    nonzero = any(re != 0 or im != 0 for row in model.amplitudes for re, im in row)
    prerequisite = Check("nonzero_prepared_two_particle_state",
        "no_counterexample_within_bounds" if nonzero else "inconclusive", 1, 1,
        "nonzero_supplied_two_particle_tensor", ASSUMPTIONS,
        None if nonzero else {"inputs": {}, "actual": "zero_tensor",
                              "required": "nonzero_for_this_prepared_two_particle_check"})
    size = len(model.modes)
    checks = [prerequisite]
    if model.statistics == "fermion":
        checks.append(run_probe("pauli_same_complete_mode", _residuals(model, diagonal=True),
                                2 * size, "=0", ASSUMPTIONS, limits))
    checks.append(run_probe("exchange_symmetry", _residuals(model, diagonal=False),
                            size * (size + 1), "=0", ASSUMPTIONS, limits))
    return tuple(checks), {
        "adapter_status": "supplied_finite_state_benchmark", "scientific_status": "unassessed",
        "origin": model.origin, "statistics": model.statistics,
        "requirement_applicability": {
            "pauli_same_complete_mode": "applicable" if model.statistics == "fermion" else "not_applicable",
            "exchange_symmetry": "applicable"},
        "state_scope": "one_supplied_finite_two_particle_tensor_not_all_states",
        "normalization": "not_required_for_homogeneous_identities_no_probability_readout",
        "zero_tensor_meaning": "inconclusive_prepared_state_not_global_vacuum_rejection",
        "unused_limits": ["coefficient_radius", "reference_radius", "max_copies"],
        "missing_bridges": ["native_primitive_to_amplitudes", "statistics_selection",
                            "physical_mode_completeness", "empirical_preparation_and_readout"],
        "untested": ["N_body", "CAR", "spin_statistics_theorem", "unique_QM",
                     "physical_probabilities_or_occupations", "empirical_data"],
    }
