"""Exact, bounded counterexample search. This module is not a proof authority."""

from __future__ import annotations

import hashlib
import itertools
import json
import re
from collections.abc import Iterable
from dataclasses import dataclass
from fractions import Fraction
from pathlib import Path
from typing import Literal, TypeAlias

Vector: TypeAlias = tuple[Fraction, ...]
Matrix: TypeAlias = tuple[Vector, ...]
Status: TypeAlias = Literal[
    "counterexample", "no_counterexample_within_bounds", "inconclusive", "unsupported"
]
SCHEMA = "idt-primitive-screen/1"
ROOT = Path(__file__).resolve().parents[1]
SOURCE_PATHS = (
    "theory_experiments/primitive_screen.py",
    "scripts/screen_primitives.py",
    "Proofs/MetaLang/V8PrimitiveScreenBoundary.lean",
)
UNTESTED = (
    "derivation_from_lower_primitives", "detector_model", "experimental_data",
    "bell_correlations", "complex_quantum_theory", "standard_model", "gravity",
)


def bounded_int(value: object, minimum: int, maximum: int) -> int:
    if type(value) is not int or not minimum <= value <= maximum:
        raise ValueError(f"expected integer in [{minimum}, {maximum}]")
    return value


def object_fields(value: object, expected: set[str] | None = None) -> dict[str, object]:
    if not isinstance(value, dict):
        raise TypeError("expected JSON object")
    result: dict[str, object] = {}
    for key, item in value.items():
        if not isinstance(key, str):
            raise TypeError("object keys must be strings")
        result[key] = item
    if expected is not None and set(result) != expected:
        raise ValueError(f"expected exactly these fields: {sorted(expected)}")
    return result


def exact_fraction(value: object) -> Fraction:
    if not isinstance(value, str) or not re.fullmatch(r"-?\d{1,12}(?:/[1-9]\d{0,11})?", value):
        raise ValueError("fractions must be bounded integer or n/d strings, never floats")
    return Fraction(value)


def candidate_id(value: object) -> str:
    if not isinstance(value, str) or not re.fullmatch(r"[a-z][a-z0-9_-]{0,63}", value):
        raise ValueError("candidate id must be a short lowercase identifier")
    return value


def quadratic(matrix: Matrix, coefficients: Vector) -> Fraction:
    return sum(
        (coefficients[i] * matrix[i][j] * coefficients[j]
         for i in range(len(matrix)) for j in range(len(matrix))), Fraction()
    )


@dataclass(frozen=True)
class PairKernel:
    id: str
    matrix: Matrix

    def __post_init__(self) -> None:
        candidate_id(self.id)
        bounded_int(len(self.matrix), 1, 3)
        if any(len(row) != self.dimension for row in self.matrix):
            raise ValueError("kernel must be square")
        if any(not isinstance(x, Fraction) for row in self.matrix for x in row):
            raise ValueError("kernel entries must be exact Fractions")
        if any(self.matrix[i][j] != self.matrix[j][i]
               for i in range(self.dimension) for j in range(self.dimension)):
            raise ValueError("this adapter supports symmetric rational kernels only")

    @property
    def dimension(self) -> int:
        return len(self.matrix)

    def weight(self, coefficients: Vector) -> Fraction:
        return quadratic(self.matrix, coefficients)

    def specification(self) -> dict[str, object]:
        return {"id": self.id, "family": "pair_kernel",
                "matrix": [[str(x) for x in row] for row in self.matrix]}


@dataclass(frozen=True)
class PowerSum:
    id: str
    dimension: int
    exponent: int

    def __post_init__(self) -> None:
        candidate_id(self.id)
        bounded_int(self.dimension, 1, 3)
        bounded_int(self.exponent, 1, 8)

    def weight(self, coefficients: Vector) -> Fraction:
        return abs(sum(coefficients, Fraction()) / self.dimension) ** self.exponent

    def specification(self) -> dict[str, object]:
        return {"id": self.id, "family": "power_sum",
                "dimension": self.dimension, "exponent": self.exponent}


Candidate: TypeAlias = PairKernel | PowerSum


def parse_candidate(value: object) -> Candidate:
    row = object_fields(value)
    if row.get("family") == "pair_kernel":
        object_fields(row, {"id", "family", "matrix"})
        matrix = row["matrix"]
        if not isinstance(matrix, list) or not 1 <= len(matrix) <= 3:
            raise ValueError("matrix must contain 1 to 3 rows")
        rows: list[Vector] = []
        for values in matrix:
            if not isinstance(values, list) or len(values) != len(matrix):
                raise ValueError("matrix must be square")
            rows.append(tuple(exact_fraction(x) for x in values))
        return PairKernel(candidate_id(row["id"]), tuple(rows))
    if row.get("family") == "power_sum":
        object_fields(row, {"id", "family", "dimension", "exponent"})
        return PowerSum(candidate_id(row["id"]), bounded_int(row["dimension"], 1, 3),
                        bounded_int(row["exponent"], 1, 8))
    raise ValueError("unsupported family; implement an explicit adapter for new semantics")


def builtin_candidates() -> dict[str, Candidate]:
    return {
        "square": PairKernel("square", ((Fraction(1, 4), Fraction(1, 4)),) * 2),
        "fourth": PowerSum("fourth", 2, 4),
        "non_psd": PairKernel("non_psd", (
            (Fraction(1, 6), Fraction(1, 3)), (Fraction(1, 3), Fraction(1, 6)))),
    }


@dataclass(frozen=True)
class Limits:
    max_cases: int = 1000
    coefficient_radius: int = 1
    reference_radius: int = 2
    max_copies: int = 2

    def __post_init__(self) -> None:
        bounded_int(self.max_cases, 1, 5000)
        bounded_int(self.coefficient_radius, 1, 2)
        bounded_int(self.reference_radius, 1, 2)
        bounded_int(self.max_copies, 1, 2)

    def specification(self) -> dict[str, object]:
        return {"max_cases": self.max_cases, "coefficient_radius": self.coefficient_radius,
                "reference_radius": self.reference_radius, "max_copies": self.max_copies}


def parse_limits(value: object) -> Limits:
    row = object_fields(value, {"max_cases", "coefficient_radius", "reference_radius", "max_copies"})
    return Limits(bounded_int(row["max_cases"], 1, 5000),
                  bounded_int(row["coefficient_radius"], 1, 2),
                  bounded_int(row["reference_radius"], 1, 2),
                  bounded_int(row["max_copies"], 1, 2))


@dataclass(frozen=True)
class Trial:
    inputs: dict[str, object]
    actual: Fraction


@dataclass(frozen=True)
class Check:
    id: str
    status: Status
    checked: int
    planned: int
    requirement: str
    assumptions: tuple[str, ...]
    witness: dict[str, object] | None

    def specification(self) -> dict[str, object]:
        return {"id": self.id, "status": self.status, "checked": self.checked,
                "planned": self.planned, "requirement": self.requirement,
                "assumptions": list(self.assumptions), "witness": self.witness}


def run_probe(check_id: str, trials: Iterable[Trial], planned: int,
              requirement: Literal["=0", "=1", ">=0"], assumptions: tuple[str, ...],
              limits: Limits) -> Check:
    checked = 0
    for trial in itertools.islice(trials, limits.max_cases):
        checked += 1
        holds = (trial.actual >= 0 if requirement == ">=0" else
                 trial.actual == (1 if requirement == "=1" else 0))
        if not holds:
            witness: dict[str, object] = {"inputs": trial.inputs, "actual": str(trial.actual),
                                         "required": requirement}
            return Check(check_id, "counterexample", checked, planned, requirement,
                         assumptions, witness)
    status: Status = "no_counterexample_within_bounds" if checked == planned else "inconclusive"
    return Check(check_id, status, checked, planned, requirement, assumptions, None)


def indicator(size: int, mask: int) -> Vector:
    return tuple(Fraction((mask >> i) & 1) for i in range(size))


def vectors(size: int, radius: int) -> tuple[Vector, ...]:
    return tuple(tuple(Fraction(x) for x in row)
                 for row in itertools.product(range(-radius, radius + 1), repeat=size))


def third_trials(candidate: Candidate, grid: tuple[Vector, ...]) -> Iterable[Trial]:
    for triple in itertools.product(grid, repeat=3):
        value = Fraction()
        for mask in range(8):
            coefficients = tuple(sum((triple[k][i] for k in range(3) if mask & (1 << k)),
                                     Fraction()) for i in range(candidate.dimension))
            value += (-1) ** (3 - mask.bit_count()) * candidate.weight(coefficients)
        yield Trial({"vectors": [[str(x) for x in row] for row in triple]}, value)


def tensor(left: Matrix, right: Matrix) -> Matrix:
    return tuple(tuple(left[i][j] * right[a][b]
                       for j in range(len(left)) for b in range(len(right)))
                 for i in range(len(left)) for a in range(len(right)))


def copy_trials(candidate: PairKernel, copies: int) -> Iterable[Trial]:
    matrix: Matrix = ((Fraction(1),),)
    for count in range(1, copies + 1):
        matrix = tensor(matrix, candidate.matrix)
        for mask in range(2 ** len(matrix)):
            event = indicator(len(matrix), mask)
            yield Trial({"copies": count, "event_mask": mask}, quadratic(matrix, event))


def reference_trials(candidate: PairKernel, grid: tuple[Vector, ...]) -> Iterable[Trial]:
    size = candidate.dimension
    diagonal = tuple(Fraction(i == j) for i in range(size) for j in range(size))
    for vector in grid:
        total = sum(vector, Fraction())
        reference = tuple(tuple(a * b / total ** 2 for b in vector) for a in vector)
        composite = tensor(candidate.matrix, reference)
        yield Trial({"reference_vector": [str(x) for x in vector],
                     "reference_matrix": [[str(x) for x in row] for row in reference],
                     "composite_event": [[i, i] for i in range(size)]},
                    quadratic(composite, diagonal))


def evaluate(candidate: Candidate, limits: Limits) -> tuple[Check, ...]:
    """The common seam: compute weights from a candidate, never accept target outputs."""
    size = candidate.dimension
    grid = vectors(size, limits.coefficient_radius)
    weights = ("rational_coefficient_carrier", "indicator_events", "candidate_weight_rule")
    checks = [
        run_probe("unit_weight", [Trial({"event_mask": 2 ** size - 1},
                  candidate.weight(indicator(size, 2 ** size - 1)))], 1, "=1", weights, limits),
        run_probe("event_nonnegative", (Trial({"event_mask": mask},
                  candidate.weight(indicator(size, mask))) for mask in range(2 ** size)),
                  2 ** size, ">=0", weights, limits),
        run_probe("coefficient_third_difference", third_trials(candidate, grid),
                  len(grid) ** 3, "=0", weights + ("coefficient_addition",
                  "quadratic_grade_requirement_not_a_laboratory_slit_test"), limits),
    ]
    copy_assumptions = weights + ("pair_kernel_representation", "tensor_multiplication",
                                 "all_indicator_events_of_composite")
    reference_assumptions = copy_assumptions + (
        "admit_normalized_signed_rank_one_references_with_nonzero_sum",)
    if isinstance(candidate, PairKernel):
        references = tuple(v for v in vectors(size, limits.reference_radius) if sum(v) != 0)
        checks.extend([
            run_probe("self_composition", copy_trials(candidate, limits.max_copies),
                      sum(2 ** (size ** k) for k in range(1, limits.max_copies + 1)),
                      ">=0", copy_assumptions, limits),
            run_probe("signed_reference_composition", reference_trials(candidate, references),
                      len(references), ">=0", reference_assumptions, limits),
        ])
    else:
        checks.extend(Check(name, "unsupported", 0, 0, ">=0", assumptions, None)
                      for name, assumptions in (("self_composition", copy_assumptions),
                          ("signed_reference_composition", reference_assumptions)))
    return tuple(checks)


def aggregate_status(checks: tuple[Check, ...]) -> Status:
    if not checks:
        return "inconclusive"
    for status in ("counterexample", "inconclusive", "unsupported"):
        if any(check.status == status for check in checks):
            return status
    return "no_counterexample_within_bounds"


def canonical_json(value: object) -> str:
    return json.dumps(value, sort_keys=True, separators=(",", ":"), allow_nan=False)


def screen(candidate: Candidate, limits: Limits | None = None) -> dict[str, object]:
    limits = limits if limits is not None else Limits()
    checks = evaluate(candidate, limits)
    spec = candidate.specification()
    return {
        "schema": SCHEMA, "candidate": spec,
        "candidate_sha256": hashlib.sha256(canonical_json(spec).encode()).hexdigest(),
        "source_sha256": {path: hashlib.sha256((ROOT / path).read_bytes()).hexdigest()
                          for path in SOURCE_PATHS},
        "limits": limits.specification(), "status": aggregate_status(checks),
        "checks": [check.specification() for check in checks],
        "arithmetic": "exact_rational", "ordering": "lexicographic_vectors_then_bitmask_events",
        "rejection_scope": "candidate_plus_stated_assumptions_and_selected_requirements",
        "evidence_kind": "bounded_computation_not_kernel_checked_proof",
        "empirical_status": "not_tested", "proof_status": "not_attempted",
        "untested": list(UNTESTED),
    }


def reject_duplicate_keys(pairs: list[tuple[str, object]]) -> dict[str, object]:
    result: dict[str, object] = {}
    for key, value in pairs:
        if key in result:
            raise ValueError(f"duplicate JSON key: {key}")
        result[key] = value
    return result


def reject_nonexact_number(value: str) -> object:
    raise ValueError(f"non-integer JSON number is forbidden: {value[:40]}")


def load_json(path: Path) -> object:
    with path.open("rb") as source:
        data = source.read(131073)
    if len(data) > 131072:
        raise ValueError("input exceeds 128 KiB limit")
    value: object = json.loads(data, object_pairs_hook=reject_duplicate_keys,
                               parse_float=reject_nonexact_number,
                               parse_constant=reject_nonexact_number)
    return value


def replay(value: object) -> dict[str, object]:
    row = object_fields(value)
    if row.get("schema") != SCHEMA or "candidate" not in row or "limits" not in row:
        raise ValueError("not a primitive-screen report")
    current = screen(parse_candidate(row["candidate"]), parse_limits(row["limits"]))
    if canonical_json(current) != canonical_json(row):
        raise ValueError("replay mismatch: inputs, results, bounds or source hashes changed")
    return current


def summary(report: dict[str, object]) -> str:
    rows = report["checks"]
    if not isinstance(rows, list):
        raise TypeError("report checks must be a list")
    lines = [f"status: {report['status']}"]
    for value in rows:
        row = object_fields(value)
        witness = row["witness"]
        actual = "" if witness is None else f"; actual={object_fields(witness)['actual']}"
        lines.append(f"  {row['id']}: {row['status']} ({row['checked']}/{row['planned']}){actual}")
    lines.append("Finite mathematical screen only. Experiments and primitive truth: NOT VERIFIED.")
    return "\n".join(lines)
