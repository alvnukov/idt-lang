"""Conditional rank holdout on supplied five-slot symmetric pencil supports.

The input is forty real rational entries, not ten arbitrary matrices. The
selection hypothesis (no rank ten) is supplied, not an observation. The
bounded adapter measures no magnitudes and does not infer a physical pencil.
"""

from __future__ import annotations

import hashlib
from collections.abc import Iterator
from dataclasses import dataclass
from fractions import Fraction
from functools import cache
from itertools import combinations, pairwise
from math import prod
from pathlib import Path

from theory_experiments.primitive_screen import (
    Check,
    Limits,
    Trial,
    candidate_id,
    exact_fraction,
    object_fields,
    run_probe,
)

LOADED_SOURCE_SHA256 = hashlib.sha256(Path(__file__).read_bytes()).hexdigest()
CHECK_ID = "chiral_pencil_rank10_holdout"
ASSUMPTIONS = (
    "supplied_symmetric_five_slot_support_with_fixed_addressed_states_and_channels",
    "nonzero_exact_real_rational_entries_only",
    "freely_combined_channels_and_absence_of_rank_ten_as_selection_hypothesis",
    "rank_only_not_a_physical_rank_readout_or_a_magnitude_prediction",
)

MASKS = tuple(m for m in range(32) if m.bit_count() % 2 == 0)
EDGES = tuple((a, b) for a, b in combinations(MASKS, 2) if (a ^ b).bit_count() == 4)


def _channel(a: int, b: int) -> int:
    slot = (31 ^ a ^ b).bit_length() - 1
    return 2 * slot + ((a >> slot) & 1)


CHANNELS = tuple(_channel(a, b) for a, b in EDGES)
# Zero-based row and column certificate of the frozen weighted pencil probe.
# These integers are verified against the generated support, not assumed.
_ROWS = (*range(17), 24, 25, 26)
_COLS = (20, 3, 11, 12, 10, 21, 7, 25, 9, 17, 1, 30, 16, 4, 15, 26, 18, 8, 22, 13)
_ENTRY_MAX = 10**12 - 1


@dataclass(frozen=True)
class ChiralPencil:
    id: str
    weights: tuple[Fraction, ...]

    def __post_init__(self) -> None:
        candidate_id(self.id)
        if type(self.weights) is not tuple or len(self.weights) != 40:
            raise ValueError("weights must be an immutable tuple of 40 exact Fractions")
        for x in self.weights:
            if (
                type(x) is not Fraction
                or not -_ENTRY_MAX <= x.numerator <= _ENTRY_MAX
                or not 1 <= x.denominator <= _ENTRY_MAX
            ):
                raise ValueError(
                    "weights require exact Fractions with at most 12 digits per part"
                )

    def specification(self) -> dict[str, object]:
        return {
            "id": self.id,
            "family": "chiral_pencil",
            "weights": list(map(str, self.weights)),
        }


def parse_chiral_pencil(value: object) -> ChiralPencil:
    row = object_fields(value, {"id", "family", "weights"})
    if row["family"] != "chiral_pencil":
        raise ValueError("expected chiral_pencil family")
    raw = row["weights"]
    if not isinstance(raw, list) or len(raw) != 40:
        raise ValueError("weights must be a 40-entry JSON array")
    return ChiralPencil(candidate_id(row["id"]), tuple(exact_fraction(x) for x in raw))


@dataclass(frozen=True)
class _Hexagon:
    channels: tuple[int, ...]
    edges: tuple[int, ...]  # cyclically ordered edge indices

    def row(self) -> list[int]:
        result = [0] * 40
        for j, edge in enumerate(self.edges):
            result[edge] = 1 if j % 2 == 0 else -1
        return result


def _hexagon(channels: tuple[int, ...]) -> _Hexagon:
    neighbors: dict[int, list[int]] = {m: [] for m in MASKS}
    for (a, b), channel in zip(EDGES, CHANNELS, strict=True):
        if channel in channels:
            neighbors[a].append(b)
            neighbors[b].append(a)
    # Each support is a hexagon, two three-edge stars, and two isolates.
    cycle = {m for m in MASKS if len(neighbors[m]) == 2}
    degrees = sorted(len(neighbors[m]) for m in MASKS)
    if (
        degrees != [0] * 2 + [1] * 6 + [2] * 6 + [3] * 2
        or any(not set(neighbors[m]) <= cycle for m in cycle)
        or any(
            len(neighbors[n]) != 1
            for ns in neighbors.values()
            if len(ns) == 3
            for n in ns
        )
    ):
        raise ArithmeticError("unexpected three-channel support")
    start = min(cycle)
    vertices = [start, min(neighbors[start])]
    while len(vertices) < 7:
        (other,) = (n for n in neighbors[vertices[-1]] if n != vertices[-2])
        vertices.append(other)
    if vertices[-1] != start or set(vertices[:-1]) != cycle:
        raise ArithmeticError("invalid hexagon")
    edges = tuple(EDGES.index((min(x, y), max(x, y))) for x, y in pairwise(vertices))
    if any({CHANNELS[j] for j in edges[k::2]} != set(channels) for k in (0, 1)):
        raise ArithmeticError("matchings have different channel monomials")
    return _Hexagon(channels, edges)


def _certify(rows: list[list[int]]) -> None:
    """Verify an integral signed basis, including the inhomogeneous -1 target.

    Unit pivots only: the first 40 entries are exponent vectors over the
    integers and the last entry tracks powers of the common target -1.
    Reconstruct every full row, not merely its projection onto 20 columns.
    """
    if len(rows) != 80 or len(set(_COLS)) != 20 or len(_ROWS) != 20:
        raise ArithmeticError("unexpected size of pencil incidence certificate")
    basis = [rows[i] + [1] for i in _ROWS]
    for k, col in enumerate(_COLS):
        pivot = basis[k][col]
        if abs(pivot) != 1:
            raise ArithmeticError("nonunit pivot in integer incidence certificate")
        basis[k] = [x * pivot for x in basis[k]]
        for j, row in enumerate(basis):
            if j != k and (factor := row[col]):
                basis[j] = [x - factor * y for x, y in zip(row, basis[k], strict=True)]
    for row in rows:
        factors = [row[col] for col in _COLS]
        recovered = [
            sum(f * x for f, x in zip(factors, column, strict=True))
            for column in zip(*basis, strict=True)
        ]
        if recovered[:-1] != row or recovered[-1] % 2 != 1:
            raise ArithmeticError(
                "integer basis does not reproduce all signed conditions"
            )


@cache
def _basis() -> tuple[_Hexagon, ...]:
    all_hexagons = tuple(
        _hexagon(t) for t in combinations(range(10), 3) if len({k // 2 for k in t}) == 3
    )
    _certify([h.row() for h in all_hexagons])
    return tuple(all_hexagons[j] for j in _ROWS)


def _unit_sum_rank(weights: tuple[Fraction, ...], channels: tuple[int, ...]) -> int:
    """Independent Gaussian elimination on the symmetric full three-channel sum."""
    matrix = [[Fraction() for _ in MASKS] for _ in MASKS]
    for (a, b), k, w in zip(EDGES, CHANNELS, weights, strict=True):
        if k in channels:
            i, j = MASKS.index(a), MASKS.index(b)
            matrix[i][j] = matrix[j][i] = w
    r = 0
    for col in range(len(MASKS)):
        pivot = next((i for i in range(r, len(MASKS)) if matrix[i][col]), None)
        if pivot is None:
            continue
        matrix[r], matrix[pivot] = matrix[pivot], matrix[r]
        for j in range(r + 1, len(MASKS)):
            if matrix[j][col]:
                scale = matrix[j][col] / matrix[r][col]
                matrix[j] = [
                    x - scale * y for x, y in zip(matrix[j], matrix[r], strict=True)
                ]
        r += 1
    return r


def _trials(candidate: ChiralPencil) -> Iterator[Trial]:
    for h in _basis():
        left, right = (
            prod((candidate.weights[j] for j in h.edges[k::2]), start=Fraction(1))
            for k in (0, 1)
        )
        inputs: dict[str, object] = {}
        if left + right != 0:
            rank = _unit_sum_rank(candidate.weights, h.channels)
            if rank != 10:
                raise ArithmeticError(
                    "hexagon residual disagrees with independent unit-sum rank"
                )
            inputs = {
                "channels_slot_common_bit": [[k // 2, k % 2] for k in h.channels],
                "channel_coefficients": [int(k in h.channels) for k in range(10)],
                "active_edges": [
                    {"masks": [a, b], "weight": str(w)}
                    for (a, b), k, w in zip(
                        EDGES, CHANNELS, candidate.weights, strict=True
                    )
                    if k in h.channels
                ],
                "hexagon_edge_indices_in_cyclic_order": list(h.edges),
                "alternating_matching_products": [str(left), str(right)],
                "actual_meaning": "sum_of_alternating_matching_products",
                "direct_symmetric_rational_rank": rank,
            }
        yield Trial(inputs, left + right)


def evaluate_chiral_pencil(
    candidate: ChiralPencil, limits: Limits
) -> tuple[tuple[Check, ...], dict[str, object]]:
    scope: dict[str, object] = {
        "scientific_status": "unassessed",
        "edge_order": [list(e) for e in EDGES],
        "mask_order": list(MASKS),
        "channel_order": "2*remaining_slot+common_bit; slots numbered from least significant bit",
        "input_domain": "exact_real_rational_only; zero_edges_are_unsupported",
        "input_support": "16 even masks; 40 unordered distance-four edges; 10 symmetric channels",
        "coverage": "20 independent signed product conditions generate all 80 distinct-slot triples",
        "budget_semantics": "max_cases counts candidate products; first counterexample stops",
        "rank_scope": "conditional rank holdout only; no observed rank law or magnitudes inferred",
        "unused_limits": ["coefficient_radius", "reference_radius", "max_copies"],
        "untested": [
            "nonreal_input_weights",
            "physical_rank_readout",
            "primitive_origin",
            "absolute_or_relative_physical_magnitudes",
            "experimental_data",
        ],
    }
    zeros = [j for j, w in enumerate(candidate.weights) if not w]
    if zeros:
        scope["unsupported_reason"] = "nonzero_support_required"
        scope["zero_edge_indices"] = zeros
        scope["stop_reason"] = "unsupported_zero_edge"
        return (Check(CHECK_ID, "unsupported", 0, 0, "=0", ASSUMPTIONS, None),), scope
    check = run_probe(
        CHECK_ID, _trials(candidate), len(_ROWS), "=0", ASSUMPTIONS, limits
    )
    scope["stop_reason"] = (
        "first_counterexample"
        if check.status == "counterexample"
        else "complete"
        if check.checked == check.planned
        else "max_cases"
    )
    return (check,), scope
