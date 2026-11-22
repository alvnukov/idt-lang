"""A sharp three-depth barrier for a supplied two-state stochastic readout.

Contract: p(t) = mu P**t r, one fixed row-stochastic P with at most two
states, one fixed preparation mu, and one fixed response r in [0,1]^2.
P, mu and r may be nonuniform; the final response may itself be stochastic.
Depth counts repetitions of the same circuit word, NOT successive shots.
No intermediate detector update, external clock, setting-dependent response,
or uncalibrated postselection is included in this contract.

Analytical argument. Write lambda = 1-up-down. Unless P is the identity,
p(t) = c + d lambda**t, with c a nonnegative stationary response. If p0>=p1,
then d>=0. For lambda<=0, p2>=p1>=p1**2. For lambda>=0,
p0*p2-p1**2 = c*d*(1-lambda)**2 >= 0, so p2>=p1**2 since p0<=1.
The antecedent matters: a two-state alternating clock gives (0,1,0).

The existing native integer walk supplies (p0,p1,p2)=(1,1/2,1/8).
Its exact minimum sup error over the stated two-state class is
e*=1-sqrt(7/8). If a competitor has p0<p1, its error is >1/4>e*.
Otherwise, error E<e* would imply
(1/2-E)**2 <= p1**2 <= p2 <= 1/8+E, a contradiction.
The absorbing comparator p(t)=a**t, a=1/2-e*, attains e*.

For conditional detected rates q, no false clicks, and total retention at
each depth at least eta>0, arbitrary outcome-dependent deletion gives
eta*q <= p <= 1-eta+eta*q. For the exact native observed triple the sharp
efficiency threshold is eta*=(sqrt(113)-7)/4. Above it the intervals force
p0>=p1 and eta**2/4 <= p2 <= 1-7*eta/8 is impossible. At eta*, an explicit
absorbing model and outcome-dependent retention attain all observed rates.
Thus no lower efficiency bound <=eta* excludes this class by these rates.

User intervals must contain the three underlying probabilities SIMULTANEOUSLY;
this program does not manufacture confidence intervals or a confidence level.
An inconclusive interval result is not a feasibility certificate. The executable
checks rational examples and exact quadratic-field boundary identities; the
general argument above is not a Lean proof. No experimental fit, probability
origin, physical state-count bound, or full QM derivation is claimed.

Run: python3 -B -O -m scripts.probe_two_state_readout_barrier
Optional diagnostic: --intervals 1:1 1/2:1/2 1/8:1/8
                     --efficiency-lower 99/100 99/100 99/100
"""

from __future__ import annotations

import argparse
import sys
from collections import Counter
from dataclasses import dataclass
from fractions import Fraction as F
from itertools import product
from pathlib import Path
from typing import Literal

if not __package__:
    sys.path.insert(0, str(Path(__file__).resolve().parents[1]))

from scripts.probe_native_recurrence_witness import native_prefix

Triple = tuple[F, F, F]
Matrix = tuple[tuple[F, ...], ...]
TARGET: Triple = (F(1), F(1, 2), F(1, 8))


def need(ok: bool, message: str) -> None:
    """Checks remain active under python -O."""
    if not ok:
        raise ValueError(message)


@dataclass(frozen=True)
class Interval:
    lo: F
    hi: F

    def __post_init__(self) -> None:
        need(0 <= self.lo <= self.hi <= 1, "interval must satisfy 0<=lo<=hi<=1")

    def __str__(self) -> str:
        return f"[{self.lo}, {self.hi}]"


Intervals = tuple[Interval, Interval, Interval]


@dataclass(frozen=True)
class Diagnostic:
    status: Literal["excluded", "inconclusive"]
    true_intervals: Intervals
    order_forced: bool
    squared_lower_minus_upper: F
    reason: str


def deletion_envelope(observed: Interval, efficiency_lower: F) -> Interval:
    """No false events; deleted trials can depend arbitrarily on the outcome."""
    need(0 < efficiency_lower <= 1, "efficiency lower bound must be in (0,1]")
    return Interval(
        efficiency_lower * observed.lo,
        1 - efficiency_lower + efficiency_lower * observed.hi,
    )


def diagnose(
    observed: Intervals, efficiencies: Triple = (F(1), F(1), F(1))
) -> Diagnostic:
    converted = tuple(
        deletion_envelope(q, eta) for q, eta in zip(observed, efficiencies, strict=True)
    )
    bounds: Intervals = (converted[0], converted[1], converted[2])
    first, second, third = bounds
    ordered = first.lo >= second.hi
    gap = second.lo**2 - third.hi
    if not ordered:
        return Diagnostic(
            "inconclusive",
            bounds,
            False,
            gap,
            "Intervals allow p0<p1; the decreasing-first-step premise is not certified.",
        )
    return Diagnostic(
        "excluded" if gap > 0 else "inconclusive",
        bounds,
        True,
        gap,
        "p0>=p1 is forced and lower(p1)^2>upper(p2)."
        if gap > 0
        else "This necessary inequality has no strict contradiction; feasibility is not proved.",
    )


def uniform_intervals(error: F) -> Intervals:
    need(error >= 0, "negative simultaneous error budget")
    bounds = tuple(Interval(max(F(0), p - error), min(F(1), p + error)) for p in TARGET)
    return bounds[0], bounds[1], bounds[2]


def predict(matrix: Matrix, initial: tuple[F, ...], response: tuple[F, ...]) -> Triple:
    size = len(matrix)
    need(size > 0 and len(initial) == len(response) == size, "state dimensions")
    need(all(len(row) == size for row in matrix), "matrix dimensions")
    need(all(x >= 0 for row in matrix for x in row), "negative transition")
    need(all(sum(row, F(0)) == 1 for row in matrix), "row normalization")
    need(all(x >= 0 for x in initial) and sum(initial, F(0)) == 1, "preparation")
    need(all(0 <= x <= 1 for x in response), "response bounds")
    state = initial
    values: list[F] = []
    for _ in range(3):
        values.append(sum((x * r for x, r in zip(state, response, strict=True)), F(0)))
        state = tuple(
            sum((state[i] * matrix[i][j] for i in range(size)), F(0))
            for j in range(size)
        )
    return values[0], values[1], values[2]


def check_two_state(up: F, down: F, initial_zero: F, r0: F, r1: F) -> str:
    values = predict(
        ((1 - up, up), (down, 1 - down)),
        (initial_zero, 1 - initial_zero),
        (r0, r1),
    )
    p0, p1, p2 = values
    error = max(abs(p - q) for p, q in zip(values, TARGET, strict=True))
    lam = 1 - up - down
    if up + down == 0:
        need(p0 == p1 == p2 and p2 >= p1**2, "identity case")
        return "identity"
    c = (down * r0 + up * r1) / (up + down)
    d = p0 - c
    need(0 <= c <= 1, "stationary response")
    need(values == (c + d, c + d * lam, c + d * lam**2), "spectral identity")
    if p0 < p1:
        need(error > F(1, 4), "increasing branch is not a close native fit")
        return "increasing first step"
    need(d >= 0, "decreasing first step gives nonnegative spectral weight")
    if lam <= 0:
        need(p2 >= p1 >= p1**2, "nonpositive-eigenvalue branch")
        branch = "nonpositive eigenvalue"
    else:
        need(p0 * p2 - p1**2 == c * d * (1 - lam) ** 2 >= 0, "moment identity")
        branch = "positive eigenvalue"
    need(p2 >= p1**2, "three-depth inequality")
    if error < F(1, 4):
        need(error_polynomial(error) <= 0, "exact near-model error barrier")
    return branch


# Exact a+b*sqrt(d) arithmetic only for the two boundary witnesses below.
# No floating-point comparison is used to decide either side of a threshold.
@dataclass(frozen=True)
class Surd:
    a: F
    b: F
    d: int

    def lift(self, other: Surd | F | int) -> Surd:
        result = other if isinstance(other, Surd) else Surd(F(other), F(0), self.d)
        need(result.d == self.d, "different quadratic fields")
        return result

    def __add__(self, other: Surd | F | int) -> Surd:
        q = self.lift(other)
        return Surd(self.a + q.a, self.b + q.b, self.d)

    def __sub__(self, other: Surd | F | int) -> Surd:
        q = self.lift(other)
        return Surd(self.a - q.a, self.b - q.b, self.d)

    def __mul__(self, other: Surd | F | int) -> Surd:
        q = self.lift(other)
        return Surd(
            self.a * q.a + self.d * self.b * q.b, self.a * q.b + self.b * q.a, self.d
        )

    def __truediv__(self, other: Surd | F | int) -> Surd:
        q = self.lift(other)
        norm = q.a**2 - self.d * q.b**2
        need(norm != 0, "zero quadratic-field divisor")
        return self * Surd(q.a / norm, -q.b / norm, self.d)

    def nonnegative(self) -> bool:
        if self.b == 0:
            return self.a >= 0
        if self.b > 0:
            return self.a >= 0 or self.d * self.b**2 >= self.a**2
        return self.a >= 0 and self.a**2 >= self.d * self.b**2

    def probability(self) -> bool:
        return self.nonnegative() and (self.lift(1) - self).nonnegative()


def error_polynomial(error: F) -> F:
    return error**2 - 2 * error + F(1, 8)


def loss_polynomial(efficiency: F) -> F:
    return 2 * efficiency**2 + 7 * efficiency - 8


def boundary_certificates() -> None:
    error = Surd(F(1), F(-1, 4), 14)
    one = error.lift(1)
    a = one / 2 - error
    p2 = a * a
    need(error * error - error * 2 + F(1, 8) == error.lift(0), "error root")
    need(a.probability() and p2.probability(), "absorbing comparator bounds")
    need(one / 2 - a == error and p2 - F(1, 8) == error, "sharp equal errors")
    need(error.nonnegative() and (one / 4 - error).nonnegative(), "root branch")
    error_lo, error_hi = F(64585653306, 10**12), F(64585653307, 10**12)
    need(error_polynomial(error_lo) > 0 > error_polynomial(error_hi), "error bracket")
    need(diagnose(uniform_intervals(error_lo)).status == "excluded", "below e*")
    need(diagnose(uniform_intervals(error_hi)).status == "inconclusive", "above e*")

    eta = Surd(F(-7, 4), F(1, 4), 113)
    one = eta.lift(1)
    need(eta * eta * 2 + eta * 7 - 8 == eta.lift(0), "efficiency root")
    need(eta.probability() and (eta - F(2, 3)).nonnegative(), "efficiency branch")
    a = eta / 2
    true = (one, a, a * a)
    need(true[2] == one - eta * F(7, 8), "loss-boundary equality")
    # Entries are retention probabilities for positive/negative outcomes.
    keep = ((eta, eta.lift(0)), (one, a / (one - a)), ((eta / 8) / true[2], one))
    for p, (yes, no), observed in zip(true, keep, TARGET, strict=True):
        need(
            p.probability() and yes.probability() and no.probability(),
            "retention bounds",
        )
        total = p * yes + (one - p) * no
        need(total == eta, "same total retention at every depth")
        need(p * yes / total == eta.lift(observed), "exact conditional observed rate")
    eta_lo, eta_hi = F(907536453183, 10**12), F(907536453184, 10**12)
    need(loss_polynomial(eta_lo) < 0 < loss_polynomial(eta_hi), "efficiency bracket")
    exact: Intervals = tuple_interval(TARGET)
    need(diagnose(exact, (eta_lo,) * 3).status == "inconclusive", "below eta*")
    need(diagnose(exact, (eta_hi,) * 3).status == "excluded", "above eta*")
    print(f"Exact minimax e*=1-sqrt(7/8), certified in ({error_lo}, {error_hi}).")
    print("Absorbing comparator a=1/2-e*: (1,a,a^2); both nonzero errors equal e*.")
    print(f"Deletion threshold eta*=(sqrt(113)-7)/4, in ({eta_lo}, {eta_hi}).")
    print(
        "At eta*: exact two-state model plus valid outcome retention reproduces the target."
    )


def tuple_interval(values: Triple) -> Intervals:
    return (
        Interval(values[0], values[0]),
        Interval(values[1], values[1]),
        Interval(values[2], values[2]),
    )


def run() -> None:
    need(tuple(native_prefix(2)) == TARGET, "native integer-walk source changed")
    branches: Counter[str] = Counter()
    grid = tuple(F(i, 4) for i in range(5))
    for up, down, initial, r0, r1 in product(grid, repeat=5):
        branches[check_two_state(up, down, initial, r0, r1)] += 1
    need(
        set(branches)
        == {
            "identity",
            "increasing first step",
            "nonpositive eigenvalue",
            "positive eigenvalue",
        },
        "branch coverage",
    )
    need(diagnose(tuple_interval(TARGET)).status == "excluded", "ideal violation")
    alternating = predict(((F(0), F(1)), (F(1), F(0))), (F(0), F(1)), (F(1), F(0)))
    need(alternating == (F(0), F(1), F(0)), "increasing countercontrol")
    need(
        diagnose(tuple_interval(alternating)).status == "inconclusive",
        "antecedent guard",
    )
    need(not diagnose(uniform_intervals(F(1, 3))).order_forced, "large-error branch")

    clock: Matrix = ((F(0), F(1), F(0)), (F(0), F(0), F(1)), (F(0), F(0), F(1)))
    need(
        predict(clock, (F(1), F(0), F(0)), TARGET) == TARGET,
        "three-state clock control",
    )
    # A fixed one-state fresh Bernoulli response is constant: freshness alone
    # does not evade the barrier. A depth-dependent response can encode the
    # target with one state, but violates the fixed-r premise and derives nothing.
    single: Matrix = ((F(1),),)
    need(predict(single, (F(1),), (F(1, 2),)) == (F(1, 2),) * 3, "fixed fresh readout")
    fresh_target = tuple(predict(single, (F(1),), (q,))[0] for q in TARGET)
    need(fresh_target == TARGET, "supplied depth-dependent fresh response")
    print("Source checked: native_prefix(2)=(1,1/2,1/8).")
    print(
        f"Exact rational grid: {sum(branches.values())} models; branches={dict(sorted(branches.items()))}."
    )
    boundary_certificates()
    print(
        "Controls: alternating (0,1,0), three-state clock, fixed and depth-dependent fresh responses."
    )
    print(
        "Conditional mathematics/executable checks only; no data fit, Lean proof, or QM closure."
    )


def parse_fraction(value: str) -> F:
    try:
        return F(value)
    except (ValueError, ZeroDivisionError) as exc:
        raise argparse.ArgumentTypeError(
            "use an exact rational or finite decimal"
        ) from exc


def parse_interval(value: str) -> Interval:
    try:
        pieces = value.split(":")
        if len(pieces) != 2:
            raise ValueError("expected lower:upper")
        return Interval(F(pieces[0]), F(pieces[1]))
    except (ValueError, ZeroDivisionError) as exc:
        raise argparse.ArgumentTypeError(str(exc)) from exc


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--intervals", nargs=3, type=parse_interval, metavar=("P0", "P1", "P2")
    )
    parser.add_argument(
        "--efficiency-lower",
        nargs=3,
        type=parse_fraction,
        default=(F(1), F(1), F(1)),
        metavar=("ETA0", "ETA1", "ETA2"),
        help="independently certified per-depth retention lower bounds; no false clicks",
    )
    args = parser.parse_args()
    efficiencies: Triple = (
        args.efficiency_lower[0],
        args.efficiency_lower[1],
        args.efficiency_lower[2],
    )
    if not all(0 < eta <= 1 for eta in efficiencies):
        parser.error("every efficiency lower bound must be in (0,1]")
    supplied: Intervals = (
        tuple_interval(TARGET)
        if args.intervals is None
        else (args.intervals[0], args.intervals[1], args.intervals[2])
    )
    run()
    result = diagnose(supplied, efficiencies)
    print("Diagnostic:", result.status, "(two-state fixed-model contract only)")
    print(
        "True-probability intervals:", ", ".join(str(x) for x in result.true_intervals)
    )
    print("Reason:", result.reason)
    print("lower(p1)^2-upper(p2)=", result.squared_lower_minus_upper)
    print(
        "Intervals and efficiency bounds must be simultaneous, external inputs; no confidence level assigned."
    )


if __name__ == "__main__":
    main()
