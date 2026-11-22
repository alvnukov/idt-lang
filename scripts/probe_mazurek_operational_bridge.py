"""Descriptive cross-reference of Mazurek primary counts and the frozen fourth-axis design.

Mazurek et al., Nat. Commun. 7, 11780 (2016), doi:10.1038/ncomms11780.
Use the two workbook tables as labelled, with no correction or choice of
polarity. Frequencies are conditional on detected coincidences within each
preparation/setting cell. This is not a replay of the published secondary
procedures, a significance test, or an identification of the native model
with the experimental apparatus.

Replay: python3 -B -O -m scripts.probe_mazurek_operational_bridge
"""

from __future__ import annotations

import json
from dataclasses import dataclass
from fractions import Fraction as F

from scripts.probe_affine_fourth_axis import ROWS, TRINE, moves, score
from scripts.probe_affine_pulse_holdouts import (
    IDENT,
    TAGS,
    Perm,
    encode,
    gates,
    need,
    plane_matrix,
    power,
)
from theory_experiments.mazurek_primary import (
    AGGREGATE_SOURCE,
    CANONICAL_SHA256,
    PREPARATIONS,
    RUN_SOURCE,
    Counts,
    Matrix,
    load_counts,
)

Table = tuple[tuple[F, ...], ...]
CountRows = tuple[tuple[int, ...], ...]
# Frozen lab -> design lookup, not a permutation selected by minimizing error.
LAB_PHASES = (0, 3, 4, 1, 2, 5)
LAB_DESIGN_ROWS: tuple[int | str, ...] = (*LAB_PHASES, "+", "-")
PRIOR_GAPS = {"deterministic": F(1, 4), "random_words": F(7, 71), "random_words_with_component_flips": F(1, 12)}
ALTERNATE_SOURCE = ((0, 0, 1), (0, 2, 4), (1, 1, 4), (3, 2, 1))
ALTERNATE_PLUS, ALTERNATE_MINUS = (1, 42, 90, 102), (22, 34, 82, 123)
ALTERNATE_EFFECT_MATRIX = (4, 2, 1, 4)
IDEAL_COUNTS: CountRows = (
    *(tuple(ROWS[(k + dial) % 6] for dial in TRINE) + (2,) for k in LAB_PHASES),
    (2, 2, 2, 4),
    (2, 2, 2, 0),
)


@dataclass(frozen=True)
class Catalog:
    fixed_equator_counts: CountRows
    pole_stock_trine_counts: CountRows
    # For each native fourth-axis map: six frozen input counts and one
    # outcome-zero count for every independent transformed pole stock.
    fourth_axis: tuple[tuple[tuple[int, ...], tuple[int, ...]], ...]
    alternate_counts: CountRows


def quarters(counts: CountRows) -> Table:
    return tuple(tuple(F(n, 4) for n in row) for row in counts)


def frequencies(matrix: Matrix) -> Table:
    """Outcome zero within each paired coincidence denominator, in lab order."""
    return tuple(tuple(F(row[j], row[j] + row[j + 1]) for j in range(0, 8, 2)) for row in matrix)


def pooled_runs(counts: Counts) -> Matrix:
    return tuple(tuple(sum(run[i][j] for run in counts.runs) for j in range(8)) for i in range(8))


def catalog() -> Catalog:
    """Replay only previously fixed native choices; no data input here."""
    w, group = gates()
    dial = [power(w, k) for k in range(6)]
    detector = frozenset(i for i in IDENT if TAGS[i][0] == 0 or TAGS[dial[5][i]][0] == 0)
    effects = [frozenset(i for i in IDENT if g[i] in detector) for g in group]
    axes = [frozenset(i for i in IDENT if dial[k][i] in detector) for k in TRINE]
    seed = encode(0, 1, 0)
    centers = (seed, w[seed], w[seed], w[w[seed]])

    def equator(source: Perm) -> list[Perm]:
        return [tuple(dial[k][i] for i in source) for k in LAB_PHASES]

    fixed = equator(centers)
    reachable = moves(centers, group)
    need(len(group) == 480 and len(set(effects)) == len(reachable) == 240, "changed reference catalog")
    trine = tuple(score(s, axes) for s in fixed)
    need(trine == tuple(row[:3] for row in IDEAL_COUNTS[:6]), "changed fixed lab trine mapping")
    pole_trine = tuple(score(s, axes) for s in reachable)
    fourth = tuple((tuple(sum(x in e for x in s) for s in fixed),
                    tuple(sum(x in e for x in s) for s in reachable)) for e in effects)

    # Literal alternate-stock witness already fixed by probe_affine_fourth_axis.
    # Do not search among alternate sources, recode outcomes, or recalibrate it.
    alternate_source = tuple(encode(*t) for t in ALTERNATE_SOURCE)
    alternate_reachable = moves(alternate_source, group)
    need(ALTERNATE_PLUS in alternate_reachable and ALTERNATE_MINUS in alternate_reachable,
         "preidentified alternate poles no longer reachable")
    matching = [e for g, e in zip(group, effects, strict=True) if plane_matrix(g) == ALTERNATE_EFFECT_MATRIX]
    need(len(matching) == 1, "preidentified alternate analyzer is not unique")
    alternate = tuple(score(s, axes + matching) for s in equator(alternate_source) + [ALTERNATE_PLUS, ALTERNATE_MINUS])
    need(alternate == IDEAL_COUNTS, "preidentified witness no longer exactly matches ideal")
    return Catalog(trine, pole_trine, fourth, alternate)


def sup_error(predicted: Table, observed: Table) -> F:
    return max(abs(x - y) for a, b in zip(predicted, observed, strict=True) for x, y in zip(a, b, strict=True))


def deterministic_minimax(family: Catalog, observed: Table) -> tuple[F, int]:
    """Exact descriptive minimum over a shared fourth axis and two independent poles.

    At a fixed fourth-axis map the plus and minus terms have disjoint stock
    choices. The minimum over their Cartesian product is the maximum of
    their separate minima and the (fixed) worst equatorial discrepancy.
    """
    errors = tuple(tuple(tuple(abs(F(n, 4) - p) for n in range(5)) for p in r) for r in observed)

    def trine_error(i: int, row: tuple[int, ...]) -> F:
        return max(errors[i][j][n] for j, n in enumerate(row))

    old = max(trine_error(i, row) for i, row in enumerate(family.fixed_equator_counts))
    plus_trine, minus_trine = (
        tuple(trine_error(i, row) for row in family.pole_stock_trine_counts) for i in (6, 7)
    )
    by_map = []
    for eq, poles in family.fourth_axis:
        eq4 = max(errors[i][3][n] for i, n in enumerate(eq))
        plus = min(max(t, errors[6][3][n]) for t, n in zip(plus_trine, poles, strict=True))
        minus = min(max(t, errors[7][3][n]) for t, n in zip(minus_trine, poles, strict=True))
        by_map.append(max(old, eq4, plus, minus))
    best = min(by_map)
    return best, by_map.count(best)


def exact(value: F) -> dict[str, str | float]:
    return {"exact": str(value), "decimal": float(value)}


def compare(family: Catalog, observed: Table) -> dict[str, object]:
    ideal = quarters(IDEAL_COUNTS)
    delta = sup_error(ideal, observed)
    best, ties = deterministic_minimax(family, observed)
    alternate_error = sup_error(quarters(family.alternate_counts), observed)
    need(alternate_error == delta, "alternate witness error differs from fixed ideal error")
    need(best >= PRIOR_GAPS["deterministic"] - delta, "deterministic minimum violates the triangle bound")
    locations = [
        {"row_index": i, "column_index": j, "preparation": PREPARATIONS[i],
         "measurement": f"M{j + 1}", "signed_observed_minus_ideal": exact(x - y)}
        for i, (lab, target) in enumerate(zip(observed, ideal, strict=True))
        for j, (x, y) in enumerate(zip(lab, target, strict=True)) if abs(x - y) == delta
    ]
    return {
        "outcome_zero_frequencies_exact_in_original_lab_order": [[str(x) for x in r] for r in observed],
        "delta_to_fixed_ideal_linf": exact(delta), "max_discrepancy_cells": locations,
        "deterministic_fixed_center_empirical_minimax_linf": exact(best),
        "number_of_native_analyzer_maps_attaining_minimum": ties,
        "fixed_center_rigorous_lower_bounds_from_ideal_gaps": {
            name: {"known_ideal_gap": exact(gap), "signed_gap_minus_delta": exact(gap - delta),
                   "nonnegative_distance_lower_bound": exact(max(F(0), gap - delta))}
            for name, gap in PRIOR_GAPS.items()
        },
        "preidentified_exact_ideal_alternate_witness_empirical_linf": exact(alternate_error),
        "fourth_axis_polarity_control_observed_P4_0_minus_P4_1": exact(observed[6][3] - observed[7][3]),
    }


def report(counts: Counts) -> dict[str, object]:
    family = catalog()
    gap, ties = deterministic_minimax(family, quarters(IDEAL_COUNTS))
    need((gap, ties) == (PRIOR_GAPS["deterministic"], 84), "deterministic ideal minimax regression")
    pooled = pooled_runs(counts)
    return {
        "scope": "descriptive primary detected-coincidence frequencies; no fit of the fixed target, statistical rejection, or secondary-procedure reconstruction",
        "doi": "10.1038/ncomms11780", "canonical_primary_counts_sha256": CANONICAL_SHA256,
        "design_source": "scripts/probe_affine_fourth_axis.py",
        "lab_preparations_in_workbook_order": PREPARATIONS, "fixed_correspondence_to_design_rows": LAB_DESIGN_ROWS,
        "fixed_design_analyzers_for_M1_M2_M3": ["D after W^0", "D after W^2", "D after W^4"],
        "column": "outcome zero; coincidence counts divided by the matching two-outcome total",
        "design_ideal_counts_out_of_four_in_lab_order": IDEAL_COUNTS,
        "preidentified_alternate_witness": {
            "source_triples": ALTERNATE_SOURCE, "encoded_plus_pole_tickets": ALTERNATE_PLUS,
            "encoded_minus_pole_tickets": ALTERNATE_MINUS, "fourth_axis_matrix": ALTERNATE_EFFECT_MATRIX,
            "replayed_counts_out_of_four_in_lab_order": family.alternate_counts,
            "fit_to_workbook": False,
        },
        "catalog_size": {"native_fourth_axis_maps": len(family.fourth_axis),
                         "independent_transforms_as_distinct_stocks_per_pole": len(family.pole_stock_trine_counts)},
        "deterministic_scope": (
            "one shared fourth-axis native map and independently transformed poles from the fixed center stock; "
            "the minimax value is invariant to exchanging the two observed pole rows and does not decide polarity"
        ),
        "lower_bound_method": "triangle inequality in entrywise L-infinity; these are distances, not significance tests",
        "original_source_orientation": {
            "mismatched_count_cells": sum(x != y for a, b in zip(counts.aggregate, pooled, strict=True)
                                          for x, y in zip(a, b, strict=True)),
            "first_six_rows_agree": counts.aggregate[:6] == pooled[:6],
            "fourth_pair_row_exchange_would_reconcile_but_is_not_applied": (
                counts.aggregate == (*pooled[:6], pooled[7], pooled[6])
            ),
            "permutation_applied": False,
            "interpretation": "Do not select an orientation by goodness of fit or infer which published source label is physically correct.",
        },
        "workbook_sources": {"aggregate": AGGREGATE_SOURCE.receipt(), "runs": RUN_SOURCE.receipt()},
        "per_run_workbook_pooled_counts_as_labelled": compare(family, frequencies(pooled)),
        "aggregate_workbook_counts_as_labelled": compare(family, frequencies(counts.aggregate)),
    }


def main() -> None:
    print(json.dumps(report(load_counts()), sort_keys=True, indent=2, allow_nan=False))


if __name__ == "__main__":
    main()
