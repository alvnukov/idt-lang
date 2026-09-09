"""Native integer pair-history operations, not a physical probability adapter."""

from __future__ import annotations

import hashlib
import itertools
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
    canonical_json,
    object_fields,
    run_probe,
)
from theory_experiments.source_candidate import (
    SourceCandidate,
    evaluate_source_candidate,
)

Amplitude: TypeAlias = tuple[int, int]
Carrier: TypeAlias = Literal["integer_scalar", "integer_plane"]
WeightRule: TypeAlias = Literal["quadratic", "quartic", "absolute", "zero"]
ASSUMPTIONS = (
    "supplied_integer_carrier_addition_multiplication_and_weight",
    "formal_histories_not_necessarily_preparable_physical_states",
    "fixed_history_weights_not_context_renormalized_probabilities",
    "selected_pair_history_laws_not_complete_QM_or_empirical_requirements",
)


@dataclass(frozen=True)
class AmplitudeAlgebra:
    id: str
    carrier: Carrier
    product_square: int
    imaginary_weight: int
    weight_rule: WeightRule = "quadratic"

    def __post_init__(self) -> None:
        candidate_id(self.id)
        if self.carrier not in ("integer_scalar", "integer_plane"):
            raise ValueError("unsupported integer carrier")
        bounded_int(self.product_square, -2, 2)
        bounded_int(self.imaginary_weight, -2, 2)
        if self.weight_rule not in ("quadratic", "quartic", "absolute", "zero"):
            raise ValueError("unsupported weight rule")
        if self.carrier == "integer_scalar" and (self.product_square or self.imaginary_weight):
            raise ValueError("scalar carrier requires zero imaginary parameters")
        if self.weight_rule == "absolute" and self.carrier != "integer_scalar":
            raise ValueError("absolute rule is only defined for the scalar carrier")

    def specification(self) -> dict[str, object]:
        return {"id": self.id, "family": "amplitude_algebra", "carrier": self.carrier,
                "product_square": self.product_square, "imaginary_weight": self.imaginary_weight,
                "weight_rule": self.weight_rule}

    def grid(self, radius: int) -> tuple[Amplitude, ...]:
        values = range(-radius, radius + 1)
        return tuple((a, b) for a in values for b in
                     (values if self.carrier == "integer_plane" else (0,)))

    def add(self, left: Amplitude, right: Amplitude) -> Amplitude:
        return left[0] + right[0], left[1] + right[1]

    def multiply(self, left: Amplitude, right: Amplitude) -> Amplitude:
        a, b = left
        c, d = right
        return a * c + self.product_square * b * d, a * d + b * c

    def weight(self, value: Amplitude) -> int:
        a, b = value
        quadratic = a * a + self.imaginary_weight * b * b
        if self.weight_rule == "zero":
            return 0
        if self.weight_rule == "absolute":
            return abs(a)
        return quadratic ** 2 if self.weight_rule == "quartic" else quadratic

    def interference(self, a: Amplitude, b: Amplitude) -> int:
        return self.weight(self.add(a, b)) - self.weight(a) - self.weight(b)

    def third_order(self, a: Amplitude, b: Amplitude, c: Amplitude) -> int:
        # Seven terms: W(empty)=0 is checked separately, not silently subtracted.
        return (self.weight(self.add(self.add(a, b), c)) - self.weight(self.add(a, b))
                - self.weight(self.add(a, c)) - self.weight(self.add(b, c))
                + self.weight(a) + self.weight(b) + self.weight(c))


def parse_amplitude_algebra(value: object) -> AmplitudeAlgebra:
    row = object_fields(value, {"id", "family", "carrier", "product_square", "imaginary_weight", "weight_rule"})
    carrier = row["carrier"]
    rule = row["weight_rule"]
    if row["family"] != "amplitude_algebra" or carrier not in ("integer_scalar", "integer_plane"):
        raise ValueError("expected amplitude_algebra with a supported integer carrier")
    if rule not in ("quadratic", "quartic", "absolute", "zero"):
        raise ValueError("unsupported weight rule")
    # Explicit branches narrow JSON objects without casts or inferred scientific semantics.
    parsed_carrier: Carrier = "integer_scalar" if carrier == "integer_scalar" else "integer_plane"
    parsed_rule: WeightRule = ("quadratic" if rule == "quadratic" else "quartic" if rule == "quartic"
                               else "absolute" if rule == "absolute" else "zero")
    return AmplitudeAlgebra(candidate_id(row["id"]), parsed_carrier,
                            bounded_int(row["product_square"], -2, 2),
                            bounded_int(row["imaginary_weight"], -2, 2), parsed_rule)


def _trials(model: AmplitudeAlgebra, grid: tuple[Amplitude, ...],
            kind: Literal["nonnegative", "third_order", "product"]) -> Iterable[Trial]:
    arity = 1 if kind == "nonnegative" else 3 if kind == "third_order" else 2
    for items in itertools.product(grid, repeat=arity):
        if kind == "nonnegative":
            actual = model.weight(items[0])
        elif kind == "third_order":
            actual = model.third_order(items[0], items[1], items[2])
        else:
            actual = (model.weight(model.multiply(items[0], items[1]))
                      - model.weight(items[0]) * model.weight(items[1]))
        yield Trial({"amplitudes": [list(item) for item in items]}, Fraction(actual))


def _interference_check(model: AmplitudeAlgebra, grid: tuple[Amplitude, ...], limits: Limits) -> Check:
    checked = 0
    planned = len(grid) ** 2
    for a, b in itertools.islice(itertools.product(grid, repeat=2), limits.max_cases):
        checked += 1
        actual = model.interference(a, b)
        if actual != 0:
            return Check("native_two_path_interference", "no_counterexample_within_bounds",
                         checked, planned, "exists_nonzero_interference", ASSUMPTIONS,
                         {"kind": "existence", "inputs": {"amplitudes": [list(a), list(b)]},
                          "actual": str(actual), "required": "!=0"})
    # Exhausting a finite box does not refute existence on the infinite carrier.
    return Check("native_two_path_interference", "inconclusive", checked, planned,
                 "exists_nonzero_interference", ASSUMPTIONS, None)


def evaluate_amplitude_algebra(model: AmplitudeAlgebra, limits: Limits) -> tuple[tuple[Check, ...], dict[str, object]]:
    grid = model.grid(limits.coefficient_radius)
    checks = (
        run_probe("native_empty_weight", [Trial({"amplitude": [0, 0]}, Fraction(model.weight((0, 0))))],
                  1, "=0", ASSUMPTIONS, limits),
        run_probe("native_unit_weight", [Trial({"amplitude": [1, 0]}, Fraction(model.weight((1, 0))))],
                  1, "=1", ASSUMPTIONS + ("unit_amplitude_convention_not_all_event_normalization",), limits),
        run_probe("native_nonnegative", _trials(model, grid, "nonnegative"), len(grid), ">=0", ASSUMPTIONS, limits),
        run_probe("native_sorkin_i3", _trials(model, grid, "third_order"), len(grid) ** 3, "=0", ASSUMPTIONS, limits),
        run_probe("native_product_weight", _trials(model, grid, "product"), len(grid) ** 2, "=0",
                  ASSUMPTIONS + ("two_amplitude_product_not_physical_tensor_closure",), limits),
        _interference_check(model, grid, limits),
    )
    sampled = grid[:limits.max_cases]
    return checks, {
        "adapter_status": "bounded_algebraic", "scientific_status": "unassessed",
        "native_law": model.specification(), "domain": "integer_coefficients_only",
        "unused_limits": ["reference_radius", "max_copies"],
        "diagnostics": {"meaning": "capabilities_only_never_rejection_requirements",
            "checked": len(sampled), "planned": len(grid), "complete_within_box": len(sampled) == len(grid),
            "unit_weight_samples": [{"amplitude": list(a), "unit_plus_weight": str(model.weight(model.add((1, 0), a)))}
                                    for a in sampled if model.weight(a) == 1],
            "nonzero_zero_weight_samples": [list(a) for a in sampled if a != (0, 0) and model.weight(a) == 0]},
        "untested": ["derivation_from_lower_primitives", "operational_preparability", "probability_readout",
                     "physical_composites", "continuous_phases", "QM", "SM", "gravity", "empirical_data"],
    }


# Reviewed full immutable source specifications, not ids, filenames or executable source text.
# Bindings retain the integer carriers of PairHistoryMeasureProbe.lean verbatim.
SOURCE_BINDINGS: dict[str, tuple[Carrier, int, int]] = {
    "803d0eb295cbdb757db6e0df4c7bf7179ae5af935ee5150f4f56b71e5c9ae871": ("integer_scalar", 0, 0),
    "53c8e04102383c93e0021e640d1ca509751e18b403b2efe0e692667be22f6aa7": ("integer_plane", -1, 1),
}


def resolve_source_algebra(candidate: SourceCandidate) -> tuple[AmplitudeAlgebra, str] | None:
    """Resolve only reviewed immutable sources; never execute their retained text."""
    key = hashlib.sha256(canonical_json(candidate.specification()).encode("utf-8")).hexdigest()
    binding = SOURCE_BINDINGS.get(key)
    return None if binding is None else (AmplitudeAlgebra(candidate.id, *binding), key)


def evaluate_archived_source(candidate: SourceCandidate, limits: Limits) -> tuple[tuple[Check, ...], dict[str, object]]:
    resolved = resolve_source_algebra(candidate)
    if resolved is None:
        return evaluate_source_candidate(candidate)
    model, key = resolved
    checks, details = evaluate_amplitude_algebra(model, limits)
    details.update({"source_specification_sha256": key, "role": candidate.role,
        "binding_relation": "direct_integer_operations_adapter",
        "missing_bridges": list(candidate.missing_bridges),
        "declared_status_at_capture": candidate.declared_status,
        "source_boundary": "exact_snapshot_binding_not_source_execution_or_checked_proof"})
    binding_check = Check("primitive_prediction_adapter", "no_counterexample_within_bounds", 1, 1,
                          "exact_reviewed_source_specification_binding", ASSUMPTIONS, None)
    return (binding_check, *checks), details
