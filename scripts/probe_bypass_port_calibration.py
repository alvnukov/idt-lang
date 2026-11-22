"""Separate fixed detector gains from the stock seen through a matched bypass.

For one mixed preparation and one chosen transposition, the three ports have
model weights b=(bypass,plus,minus). Cycle the three ports through three
detectors BEFORE reading. In wiring r, branch i is sent to detector (r+i)%3.
Allow arbitrary positive incident flux per wiring and arbitrary positive,
fixed per-detector efficiencies. Pre-router branch losses are NOT removed.
No measured rows are included. Default execution uses only synthetic controls.
"""

import argparse
import json
from collections import Counter
from fractions import Fraction as F
from functools import cache
from itertools import product
from math import comb, prod
from pathlib import Path

from scripts.probe_triangle_stock_rigidity import need, outputs, quadratic
from theory_experiments.primitive_screen import load_json, object_fields

V = (2, 1, -3)
NULL = (quadratic(V), *outputs(quadratic, V, 0))
ALT = (2 * NULL[0], *NULL[1:])


def mean(b, flux, eff):
    return tuple(
        tuple(flux[r] * eff[d] * b[(d - r) % 3] for d in range(3)) for r in range(3)
    )


def products(rows):
    return tuple(prod(rows[r][(r + i) % 3] for r in range(3)) for i in range(3))


def margins(tab):
    return tuple(map(sum, tab)), tuple(map(sum, zip(*tab, strict=True)))


@cache
def row_weight(row, probs):
    a, b, c = row
    return (
        comb(a + b + c, a)
        * comb(b + c, b)
        * prod(p**n for p, n in zip(probs, row, strict=True))
    )


def fiber(rows, cols, bs):
    """Unnormalized conditional counts under independent Poisson cells.

    The same cancellation works with fixed issued/click totals per wiring
    when each row follows its multinomial model. Conditioning on detector
    totals removes detector efficiencies: all nuisance row/column factors
    are constant on this fiber. This is not a memory-robust test.
    """
    need(sum(rows) == sum(cols), "incompatible margins")
    ps = tuple(tuple(bs[(d - r) % 3] for d in range(3)) for r in range(3))
    hist = Counter()
    for a in range(min(rows[0], cols[0]) + 1):
        for b in range(max(0, rows[0] - a - cols[2]), min(rows[0] - a, cols[1]) + 1):
            c = rows[0] - a - b
            l, m, n = (cols[0] - a, cols[1] - b, cols[2] - c)
            w = row_weight((a, b, c), ps[0])
            for x in range(min(l, rows[1]) + 1):
                for y in range(max(0, rows[1] - x - n), min(m, rows[1] - x) + 1):
                    z = rows[1] - x - y
                    last = (l - x, m - y, n - z)
                    diag = a + y + last[2]
                    hist[diag] += (
                        w * row_weight((x, y, z), ps[1]) * row_weight(last, ps[2])
                    )
    return hist


def right(hist, t):
    return F(sum(v for k, v in hist.items() if k >= t), sum(hist.values()))


def controls():
    need(NULL == (7, 12, 16) and ALT == (14, 12, 16), "mixed input")
    # An independent, possibly low detection efficiency is not the same as
    # prior branch-specific filtering. Only compare these as expectation rows.
    for b in (NULL, ALT):
        rows = mean(b, (2, 7, 3), (3, 2, 5))
        w = products(rows)
        need(
            all(
                w[i] * b[j] ** 3 == w[j] * b[i] ** 3
                for i, j in product(range(3), repeat=2)
            ),
            "stationary detector response did not cancel",
        )
        need(
            F(rows[0][0], sum(rows[0])) != F(b[0], sum(b)), "single-wiring bias control"
        )
    # b' followed by 50% loss on the bypass *before* cyclic rewiring
    # coincides with b at all settings; bypass acceptance must be controlled.
    need(
        mean((ALT[0] // 2, *ALT[1:]), (2, 7, 3), (3, 2, 5))
        == mean(NULL, (2, 7, 3), (3, 2, 5)),
        "upstream loss masquerading as stock",
    )
    # Independent tiny oracle: all allocations of three labeled detections
    # in each of three wirings; condition their totals to (3,3,3).
    small = Counter()
    for labels in product(range(3), repeat=9):
        if sorted(labels) != [0] * 3 + [1] * 3 + [2] * 3:
            continue
        t = sum(d == i // 3 for i, d in enumerate(labels))
        small[t] += prod(NULL[(d - i // 3) % 3] for i, d in enumerate(labels))
    need(
        small == fiber((3,) * 3, (3,) * 3, NULL),
        "conditional likelihood independent enumeration",
    )
    # On a fixed margin the relative weight alt/null equals 2^T, T=#bypass
    # (a diagonal count). This gives the ordering, but the following tails
    # are evaluated against the conditional distributions, not raw ratios.
    n = (20,) * 3
    x = fiber(n, n, NULL)
    y = fiber(n, n, ALT)
    need(all(y[t] == (2**t) * h for t, h in x.items()), "conditional tilt")
    threshold = next(t for t in sorted(x) if right(x, t) <= F(1, 20))
    print(
        "Three cyclic wirings cancel fixed detector losses and arbitrary per-wiring flux at the mean level."
    )
    print(
        "Synthetic fixed row and column margins (20,20,20): reject for bypass count ≥",
        threshold,
        "; conditional null tail",
        float(right(x, threshold)),
        "; conditional alternative power",
        float(right(y, threshold)),
        "(not unconditional power and not measured).",
    )
    print(
        "A 1/2 pre-router bypass loss fakes the entire baseline from the alternative."
    )


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--table",
        type=Path,
        help="optional conditional comparison, 3×3 observed counts; see source",
    )
    opt = parser.parse_args()
    if opt.table is None:
        controls()
        return
    row = object_fields(load_json(opt.table), {"protocol", "counts"})
    tab = row["counts"]
    if (
        row["protocol"] != "cyclic_bypass_2_1_minus3_v1"
        or not isinstance(tab, list)
        or len(tab) != 3
        or any(
            not isinstance(r, list)
            or len(r) != 3
            or any(type(x) is not int or not 0 <= x <= 90 for x in r)
            for r in tab
        )
    ):
        parser.error(
            "expected the fixed protocol and three rows (wirings) of three detector counts"
        )
    rows, cols = margins(tab)
    if min(*rows, *cols) <= 0 or sum(rows) > 90:
        parser.error(
            "all margins must be positive and total counts at most 90 for this exact implementation"
        )
    h = fiber(rows, cols, NULL)
    t = sum(tab[i][i] for i in range(3))
    p = right(h, t)
    print(
        json.dumps(
            {
                "bypass_count": t,
                "row_totals": rows,
                "detector_totals": cols,
                "conditional_null_tail": str(p),
                "approximate_tail": float(p),
                "interpretation": "valid_only_if_source_shape_port_assignment_and_poisson_or_multinomial_model_hold",
                "empirical_candidate_verdict": "not_assessed",
            }
        )
    )


if __name__ == "__main__":
    main()
