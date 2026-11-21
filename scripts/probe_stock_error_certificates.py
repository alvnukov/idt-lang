"""Finite, exact error certificates for individual whole-port stock contrasts.

Use the standard integral chart, the fixed raw mixer of probe_port_stock_origin,
known gain h=4, and W_p(0)=0 exactly. The 625 preparations are ordered as in
that probe. A row's residual in STOCK units is

  R(x,y)= W0(out0)+W1(out1)-4 W0(x)-4 W1(y).

Rows need not vanish. We select an exact independent basis from a small
neighborhood of the original rows, keeping the original preparation IDs.
For each requested contrast d we return rational coefficients c satisfying
d = sum_i c_i row_i as an equality of linear forms on arbitrary port stocks.
Thus |d(W)| <= sum_i |c_i| eps_i when |R_i(W)| <= eps_i simultaneously.
Uniform budgets give the reported factor times eps, not a condition number
of the entire inverse problem. The certificates are not claimed optimal.
The calibration anchor is W0((1,0)). If it is only known to within delta,
add |k| delta when comparing a stock to k times its reported calibration.

The budgets must apply to the same local stock functions in common units,
under the same fixed gain, chart and gate. A port probability is not itself
a stock residual. Unknown gains, setting-dependent drift or selection,
and non-simultaneous error intervals are not accounted for automatically.
No experimental data or universal law inferred.

Run: python3 -O -m scripts.probe_stock_error_certificates [--show-rows]
"""

import argparse
from collections.abc import Hashable, Mapping
from fractions import Fraction as F
from itertools import combinations, product
from typing import TypeVar

from scripts.probe_native_recurrence_witness import native_prefix
from scripts.probe_port_stock_origin import ZERO, Quarter, Vec, grid

Label = tuple[int, Vec]
Form = dict[Label, F]
Certificate = dict[int, F]
Prep = tuple[Vec, Vec]
Key = TypeVar("Key", bound=Hashable)
ROOT = Quarter(0, -1, 1)
ANCHOR: Label = (0, (1, 0))
TARGETS: tuple[tuple[Label, int], ...] = (
    ((0, (1, 1)), 2),
    ((0, (2, 0)), 4),
    ((1, (1, 0)), 1),
    ((0, (-1, 0)), 1),
)
# Offline support search used only the known row matrix, no stock observations.
# Store row IDs, NOT floating-point weights. Recompute the unique coefficients
# on these supports and verify independence and each dual identity exactly.
# fmt: off
SUPPORTS = (
    (186,188,212,262,282,286,287,292,306,310,314,316,318,332,337,338,342,362,412,416,437,462,468),
    (156,162,168,216,262,282,287,292,302,307,308,311,313,314,316,318,322,337,342,416,436,437,
     438,442,456,462,562),
    (168,186,188,216,262,282,287,292,310,311,313,314,316,317,318,322,332,337,342,362,408,412,
     432,436,437,438,456,462,562),
    (62,156,162,182,187,188,208,212,282,292,302,306,308,316,317,318,322,332,342,412,416,437,438,462,562),
)
# fmt: on


def need(test: bool, reason: str) -> None:
    if not test:
        raise ValueError(reason)


def axpy(a: dict[Key, F], b: Mapping[Key, F], factor: F) -> None:
    for key, value in b.items():
        result = a.get(key, F(0)) + factor * value
        if result:
            a[key] = result
        else:
            a.pop(key, None)


def gain_row(prep: Prep) -> Form:
    x, y = prep
    u, v = ROOT.mix(x, y)
    row: Form = {}
    for port, z, coeff in ((0, x, -4), (1, y, -4), (0, u, 1), (1, v, 1)):
        if z != ZERO:
            axpy(row, {(port, z): F(coeff)}, F(1))
    return row


def norm(z: Vec) -> int:
    return z[0] ** 2 + z[1] ** 2


def size(prep: Prep) -> int:
    return max(map(norm, (*prep, *ROOT.mix(*prep))))


def certificates(preps: list[Prep], rows: list[Form]) -> dict[Label, Certificate]:
    # Finite local rows with fixed support. Every pivot traces to an original
    # row ID. No signed-port or common-port equality is inserted as a constraint.
    basis: dict[Label, tuple[Form, Certificate]] = {}

    def eliminate(row: Form, trace: Certificate) -> None:
        while row:
            p = min(row)
            if p not in basis:
                break
            other, origin = basis[p]
            factor = -row[p]
            axpy(row, other, factor)
            axpy(trace, origin, factor)

    out = {}
    for (label, k), order in zip(TARGETS, SUPPORTS, strict=True):
        basis.clear()
        for i in order:
            need(0 <= i < len(rows) and size(preps[i]) <= 8, "nonlocal original row")
            row, trace = rows[i].copy(), {i: F(1)}
            eliminate(row, trace)
            need(bool(row), "dependent original rows on this support")
            p = min(row)
            coeff = row[p]
            basis[p] = (
                {k: v / coeff for k, v in row.items()},
                {k: v / coeff for k, v in trace.items()},
            )

        target = {label: F(1), ANCHOR: F(-k)}
        rem, trace = target.copy(), {}
        eliminate(rem, trace)
        need(not rem, "contrast not spanned on this neighborhood")
        c = {i: -v for i, v in trace.items()}
        # Independently reconstruct the target vector, not just its value at
        # a square law, and do so using untouched original measurement rows.
        replay: Form = {}
        for i, v in c.items():
            axpy(replay, rows[i], v)
        need(replay == target, "dual identity against original preparations")
        out[label] = c
    return out


def bound(c: Certificate, budgets: Mapping[int, F]) -> F:
    need(
        all(i in budgets and budgets[i] >= 0 for i in c),
        "negative or missing residual budget",
    )
    return sum((abs(v) * budgets[i] for i, v in c.items()), F(0))


def evaluate(form: Form, stock: Mapping[Label, F]) -> F:
    return sum((v * stock[k] for k, v in form.items()), F(0))


def design_fixed_stock_test() -> None:
    """Choose short model tests without looking at any detector data.

    A single fixed n-atom equiprobable stock has rates k/n. Three arbitrary
    nonuniform atoms with deterministic binary responses at three settings
    give a point in one of the triangles of the Boolean cube. In three
    dimensions the nearest supporting plane gives the exact noiseless
    distance: each normal has entries in {-1,0,1} and integer offset, so
    every vertex of the cube/plane slice is integral (fix two coordinates
    at endpoints). Its polygon is a union of vertex triangles. The nearest
    plane distance is at most the distance to any cube face, so projecting
    optimally in the sup norm cannot require stepping outside the cube. Fresh
    stochastic responses and preparation-dependent weights are not covered.
    """
    ps = native_prefix(12)
    need(
        ps[2] == F(1, 8) and abs(ps[2] - ps[2].limit_denominator(4)) == F(1, 8),
        "four equal atoms",
    )

    # If a fraction eta or more of arrivals is recorded (no false clicks),
    # q is conditional on recording. Adversarial loss gives this FULL
    # interval for the emitted rate, not the deconditioned point estimate q.
    def interval(q: F, eta: F) -> tuple[F, F]:
        return eta * q, 1 - eta * (1 - q)

    lo, hi = interval(F(1, 8), F(6, 7))
    need(lo > 0 and hi == F(1, 4), "loss boundary admits four equal atoms")
    need(interval(F(1, 8), F(7, 8))[1] < F(1, 4), "above certified efficiency")
    corners = list(product((0, 1), repeat=3))
    planes: set[tuple[tuple[int, ...], int]] = set()
    for a, b, c in combinations(corners, 3):
        u = [y - x for x, y in zip(a, b, strict=True)]
        v = [y - x for x, y in zip(a, c, strict=True)]
        n = tuple(
            u[(i + 1) % 3] * v[(i + 2) % 3] - u[(i + 2) % 3] * v[(i + 1) % 3]
            for i in range(3)
        )
        need(max(map(abs, n)) == 1, "integral cube slice with unit coefficients")
        planes.add((n, sum(x * y for x, y in zip(n, a, strict=True))))

    def lower(ts: tuple[int, ...], gate_delta: F = F(0)) -> F:
        return min(
            (
                abs(sum((ps[t] * n[i] for i, t in enumerate(ts)), F(0)) - k)
                - sum((abs(n[i]) * 2 * t * gate_delta for i, t in enumerate(ts)), F(0))
            )
            / sum(map(abs, n))
            for n, k in planes
        )

    first = lower((1, 2, 3))
    tight = (F(1, 2), F(9, 64), F(9, 64))
    need(
        first
        == max(abs(x - y) for x, y in zip(tight, ps[1:4], strict=True))
        == F(1, 64),
        "sharp three-atom first tests",
    )
    # These masses on 000,011,100 attain the supporting plane at the stated point.
    witness = tuple(
        sum(
            w * corner[i]
            for w, corner in (
                (F(23, 64), (0, 0, 0)),
                (F(9, 64), (0, 1, 1)),
                (F(32, 64), (1, 0, 0)),
            )
        )
        for i in range(3)
    )
    need(witness == tight, "nonuniform boundary witness")
    # Add a fourth state: the first three settings can be reproduced EXACTLY.
    four = tuple(
        sum(
            w * corner[i]
            for w, corner in (
                (F(4, 32), (1, 1, 1)),
                (F(1, 32), (1, 0, 1)),
                (F(11, 32), (1, 0, 0)),
                (F(16, 32), (0, 0, 0)),
            )
        )
        for i in range(3)
    )
    need(four == tuple(ps[1:4]), "four-atom competitor")
    bound_value, chosen = max((lower(ts), ts) for ts in combinations(range(1, 13), 3))
    need(
        chosen == (3, 9, 12) and bound_value == F(864387, 16777216), "short-word design"
    )
    # An explicit closest stock: masses on 000, 010 and 101. This attains,
    # not merely approaches, the sharp lower bound at the selected design.
    shared = (ps[3] + ps[12]) / 2
    masses = (1 - ps[9] - shared, ps[9], shared)
    need(
        min(masses) >= 0
        and sum(masses) == 1
        and max(abs(ps[3] - shared), abs(ps[12] - shared)) == bound_value,
        "attainability with three fixed atoms",
    )
    # T contains two gates per round. For fixed norm-one unitaries, telescoping
    # gives vector error <=2t delta at calibrated operator error delta per gate.
    # Every fixed projector changes by at most pure-state trace distance, itself
    # <= vector error. This calibration model is a control, not lab evidence.
    robust, shorter = max(
        (lower(ts, F(1, 500)), ts) for ts in combinations(range(1, 13), 3)
    )
    need(shorter == (3, 4, 9) and robust == F(427, 32000), "noisy word design")
    print(
        "Uniform ≤4 atoms: t=2, p=1/8, gap 1/8. At observed q=1/8, adversarial losses retain exclusion only if certified efficiency >6/7 (no false counts)."
    )
    print(
        f"Fixed ≤3 possibly unequal atoms: t=(1,2,3) minimax error 1/64; best noiseless design among 220 short triples: {chosen}, sharp gap {bound_value}."
    )
    print(
        f"At hypothetical per-gate operator error ≤1/500 the best certified triple changes to {shorter}, surviving gap ≥{robust}."
    )
    print(
        "All designs are against deterministic readout on one fixed stock, not arbitrary classical noise; no detector data fitted."
    )


def main() -> None:
    parser = argparse.ArgumentParser(
        description="Exact local stock error certificates."
    )
    parser.add_argument(
        "--show-rows",
        action="store_true",
        help="print original input pairs and rational coefficients",
    )
    args = parser.parse_args()
    points = grid(2)
    preps = list(product(points, points))
    rows = [gain_row(x) for x in preps]
    touched = {k for row in rows for k in row}
    need(len(preps) == 625 and len(touched) == 184, "original input grid")
    certs = certificates(preps, rows)
    ideal = {k: F(norm(k[1])) for k in touched}
    # Deterministic signed perturbations, including differing port responses;
    # keep the anchor fixed. Falsifies the zero-residual model on this grid.
    noisy = {
        k: v + F(((11 * k[0] + 3 * k[1][0] + k[1][1]) % 5) - 2, 100)
        for k, v in ideal.items()
    }
    noisy[ANCHOR] = ideal[ANCHOR]
    residuals = [evaluate(row, noisy) for row in rows]
    eps = {i: abs(r) for i, r in enumerate(residuals)}
    need(any(eps.values()), "perturbation must be visible")
    altered = []
    print(
        f"625 original gain rows; {sum(size(x) <= 8 for x in preps)} local candidates, squared chart radius ≤8."
    )
    for label, k in TARGETS:
        c = certs[label]
        d = noisy[label] - k * noisy[ANCHOR]
        observed = sum((v * residuals[i] for i, v in c.items()), F(0))
        need(
            d == observed and abs(d) <= bound(c, eps), "heterogeneous residual interval"
        )
        altered.append(d)
        factor = sum((abs(v) for v in c.values()), F(0))
        print(
            f"W{label[0]}{label[1]} − {k}·W0(1,0): {len(c)} rows; |contrast| ≤ ({factor})·ε with uniform bounds."
        )
        if args.show_rows:
            for i, v in sorted(c.items()):
                print(f"    {v} × R{preps[i]}  [original row {i}, zero-based]")
    need(any(altered), "perturbation must alter an individual contrast")
    hidden: Label = (0, (20, 0))
    need(hidden not in touched, "spoof must be outside the entire 625-row grid")
    outside = gain_row((hidden[1], ZERO))
    spoof = ideal | {k: F(norm(k[1])) for k in outside}
    spoof[hidden] += 1
    need(
        all(evaluate(r, spoof) == 0 for r in rows) and evaluate(outside, spoof) == -4,
        "out-of-grid spoof",
    )
    print("All 625 residuals can vanish while an untested preparation has residual −4.")
    design_fixed_stock_test()


if __name__ == "__main__":
    main()
