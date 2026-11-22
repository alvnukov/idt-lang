"""Exact split-gain check for a supplied stock on the labelled neutral triangle.

Each residue of (a,b) mod m carries a sum of squares of integer affine forms.
Both branch maps are integer linear, so on one input residue their output
residues are fixed. The gain residual in the translated grid coordinates is
therefore a polynomial of total degree <= 2. Its value at zero, its first
and pure second differences on both axes, and its mixed difference determine
it completely. All six are known from the triangular stencil below. This is
an all-integer identity test for this submitted model only, not a derivation
of any physical stock, branch readout, or theorem about arbitrary functions.
"""

from __future__ import annotations

import hashlib
from collections.abc import Iterator
from dataclasses import dataclass
from fractions import Fraction
from itertools import product
from pathlib import Path

from theory_experiments.primitive_screen import (
    Check, Limits, Trial, bounded_int, candidate_id, exact_fraction, object_fields, run_probe,
)

LOADED_SOURCE_SHA256 = hashlib.sha256(Path(__file__).read_bytes()).hexdigest()
CHECK_ID = "triangle_stock_split_gain"
SCOPE = "only_submitted_quasipolynomial_and_gain_law"
ASSUMPTIONS = (
    "all_labelled_neutral_integer_triples_available_as_inputs",
    "one_boundary_only_stock_on_inputs_and_both_outputs",
    "three_fixed_port_transpositions_and_ordinary_sum_of_two_branch_stocks",
    "supplied_positive_state_independent_exact_gain_per_fixed_port",
    "nontrivial_stock_and_zero_origin_for_this_adapter",
)
_STENCIL = ((0, 0), (1, 0), (0, 1), (2, 0), (1, 1), (0, 2))
Form = tuple[int, int, int]
Forms = tuple[Form, ...]
Residue = tuple[int, int]
Triple = tuple[int, int, int]


def _forms(raw: object, container: type) -> Forms:
    if type(raw) is not container or len(raw) > 5:
        raise ValueError("expected at most five affine forms")
    result = []
    for form in raw:
        if type(form) is not container or len(form) != 3:
            raise ValueError("an affine form is [kx,ky,c]")
        x, y, c = (bounded_int(z, -64, 64) for z in form)
        # Permuting terms, negating one whole form, or omitting zero does not
        # change a sum of squares. Repeated nonzero terms remain significant.
        first = x or y or c
        if first:
            result.append((x, y, c) if first > 0 else (-x, -y, -c))
    return tuple(sorted(result))


@dataclass(frozen=True)
class TriangleStock:
    id: str
    modulus: int
    default_forms: Forms
    overrides: tuple[tuple[Residue, Forms], ...]
    gains: tuple[Fraction, Fraction, Fraction]

    def __post_init__(self) -> None:
        candidate_id(self.id)
        m = bounded_int(self.modulus, 1, 7)
        default = _forms(self.default_forms, tuple)
        if type(self.overrides) is not tuple or len(self.overrides) > m * m:
            raise ValueError("too many residue overrides or mutable override collection")
        table = {}
        for item in self.overrides:
            if type(item) is not tuple or len(item) != 2:
                raise ValueError("expected immutable residue/forms pair")
            r, forms = item
            if type(r) is not tuple or len(r) != 2:
                raise ValueError("expected immutable pair of residues")
            key = tuple(bounded_int(z, 0, m - 1) for z in r)
            if key in table:
                raise ValueError("duplicate residue override")
            table[key] = _forms(forms, tuple)
        if (type(self.gains) is not tuple or len(self.gains) != 3
                or any(type(g) is not Fraction or not (0 < g.numerator < 10**12)
                       or g.denominator >= 10**12 for g in self.gains)):
            raise ValueError("expected three positive exact gains with <=12 digits per part")
        object.__setattr__(self, "default_forms", default)
        object.__setattr__(self, "overrides",
                           tuple(sorted((r, f) for r, f in table.items() if f != default)))

    def specification(self) -> dict[str, object]:
        return {"id": self.id, "family": "triangle_stock", "modulus": self.modulus,
                "default_forms": list(map(list, self.default_forms)),
                "overrides": [{"residue": list(r), "forms": list(map(list, f))}
                              for r, f in self.overrides],
                "gains": list(map(str, self.gains))}


def parse_triangle_stock(value: object) -> TriangleStock:
    row = object_fields(value, {"id", "family", "modulus", "default_forms", "overrides", "gains"})
    if row["family"] != "triangle_stock":
        raise ValueError("expected triangle_stock family")
    m = bounded_int(row["modulus"], 1, 7)
    overrides, gains = row["overrides"], row["gains"]
    if type(overrides) is not list or len(overrides) > m * m:
        raise ValueError("overrides must be a list of at most modulus squared entries")
    if type(gains) is not list or len(gains) != 3:
        raise ValueError("gains must be a list indexed by the three fixed ports")
    entries = []
    for raw in overrides:
        item = object_fields(raw, {"residue", "forms"})
        r = item["residue"]
        if type(r) is not list or len(r) != 2:
            raise ValueError("residue must be [a mod m,b mod m]")
        entries.append((tuple(r), _forms(item["forms"], list)))
    return TriangleStock(candidate_id(row["id"]), m, _forms(row["default_forms"], list),
                         tuple(entries), tuple(map(exact_fraction, gains)))


def _branches(v: Triple, fixed: int) -> tuple[Triple, Triple]:
    p = list(v)
    j, k = (fixed + 1) % 3, (fixed + 2) % 3
    p[j], p[k] = p[k], p[j]
    return tuple(x + y for x, y in zip(v, p)), tuple(x - y for x, y in zip(v, p))


def evaluate_triangle_stock(candidate: TriangleStock, limits: Limits
                            ) -> tuple[tuple[Check, ...], dict[str, object]]:
    m = candidate.modulus
    table = dict(candidate.overrides)
    residues = tuple(product(range(m), repeat=2))

    def stock(v: Triple) -> int:
        a, b, _ = v
        forms = table.get((a % m, b % m), candidate.default_forms)
        return sum((x * a + y * b + c)**2 for x, y, c in forms)

    def ray(unit: Triple) -> dict[str, object]:
        # At two scales per residue a vanishing sum of real squares forces
        # each affine form along this line to vanish identically there.
        def value(t: int) -> int:
            return stock(tuple(t * x for x in unit))
        first = next((t for t in range(1, 2 * m + 1) if value(t)), None)
        return {"direction": list(unit), "positive_unit_stock": value(1),
                "negative_unit_stock": value(-1),
                "first_positive_lit_scale": first,
                "stock_at_first_positive_lit_scale": value(first) if first is not None else None,
                "identically_dark_on_integer_ray": first is None}

    zero = stock((0, 0, 0))
    # A nonempty canonical form list cannot vanish on an entire full-rank coset.
    has_stock = any(table.get(r, candidate.default_forms) for r in residues)
    scope: dict[str, object] = {
        "scientific_status": "unassessed", "rejection_scope": SCOPE,
        "proof_status": "not_attempted", "empirical_status": "not_tested",
        "origin_stock": zero, "identically_zero_stock": not has_stock,
        "edge_stock": [ray(e) for e in ((0, 1, -1), (-1, 0, 1), (1, -1, 0))],
        "median_stock": [ray(e) for e in ((2, -1, -1), (-1, 2, -1), (-1, -1, 2))],
        "stencil": list(map(list, _STENCIL)),
        "case_order": "lexicographic_residue_pair_then_fixed_port_0_1_2_then_stencil",
        "budget_semantics": "max_cases_counts_gain_residuals; ray_descriptors_are_separate",
        "unused_limits": ["coefficient_radius", "reference_radius", "max_copies"],
        "identity_certified_on_submitted_integer_domain": False,
    }
    if zero or not has_stock:
        scope["stop_reason"] = "unsupported_nonzero_origin" if zero else "unsupported_zero_stock"
        return (Check(CHECK_ID, "unsupported", 0, 0, "=0", ASSUMPTIONS, None),), scope

    def trials() -> Iterator[Trial]:
        for a, b in residues:
            for fixed, gain in enumerate(candidate.gains):
                for i, j in _STENCIL:
                    x, y = a + m * i, b + m * j
                    v = (x, y, -x-y)
                    plus, minus = _branches(v, fixed)
                    w, wp, wm = stock(v), stock(plus), stock(minus)
                    residual = wp + wm - gain * w
                    inputs = ({"input": list(v), "input_residue": [a, b],
                               "stencil_offset": [i, j], "fixed_port": fixed,
                               "plus_output": list(plus), "minus_output": list(minus),
                               "input_stock": w, "plus_stock": wp, "minus_stock": wm,
                               "claimed_gain": str(gain),
                               "actual_meaning": "plus_stock+minus_stock-claimed_gain*input_stock"}
                              if residual else {})
                    yield Trial(inputs, residual)

    check = run_probe(CHECK_ID, trials(), len(residues) * 3 * len(_STENCIL), "=0",
                      ASSUMPTIONS, limits)
    passed = check.status == "no_counterexample_within_bounds"
    scope["identity_certified_on_submitted_integer_domain"] = passed
    scope["stop_reason"] = ("complete" if passed else "first_counterexample"
                            if check.status == "counterexample" else "max_cases")
    return (check,), scope
