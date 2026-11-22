"""Mixture holdout in the frozen three-cell F5 apparatus; no new pulse calibration.

P_k has four fair tickets at phases k,k+1,k+1,k+2 of the center seed.
M_k is a fair choice between P_k and P_(k+3). One common word g is applied
after preparation, then the same terminal first-wire detector is used for
all mixtures. No intermediate decisions. Baseline dial powers all return
one half. A single right contact gives 4,3,5 out of eight. A wire swap
(two left contacts) accepts 1,2,1 and has an even stronger property: its
second-minus-first difference 1/8 survives *every* nonnegative probability
stock on all 125 triples giving the same six solo rates with this W and D.
The fixed background tag is zero. The readout is unchanged, not retuned.

In a separately certified qubit sector with antipodal pure states, each
equal opposite mixture has density I/2: every common effect gives equal
rates (not necessarily 1/2 for an arbitrary effect). The six-dial table
alone does not certify those states, a two-dimensional physical sector,
or tomographic completeness. Here the enlarged measurement set explicitly
breaks operational equivalence. This is NOT a preparation-contextuality
violation, an experimental exclusion, or a conclusion about general F5
devices. Counts are model rates, not observed frequencies or error bars.

Run: python3 -B -O -m scripts.probe_affine_preparation_mixtures
"""

from collections import Counter
from fractions import Fraction as F
from itertools import permutations, product

from scripts.probe_affine_pulse_holdouts import (
    IDENT,
    TAGS,
    Perm,
    contacts,
    encode,
    gates,
    measure,
    need,
    power,
    then,
)

TARGET = (4, 3, 1, 0, 1, 3)


def transformed(i: int, scale: int, offset: int = 0) -> int:
    x, y, z = TAGS[i]
    return encode(
        (scale * x + offset) % 5, (scale * y + offset) % 5, (scale * z + offset) % 5
    )


def stock_weights(a: F, c: F) -> tuple[F, ...]:
    """All probabilities after aggregating the four common nonzero tag scalings."""
    return (a, F(1, 4) - c, c, F(1, 2) - a - c, a, F(1, 4) - a, c)


def main() -> None:
    w, group = gates()
    left, right = contacts()
    dial = [power(w, j) for j in range(6)]
    detector = frozenset(
        i for i in IDENT if TAGS[i][0] == 0 or TAGS[dial[5][i]][0] == 0
    )
    seed = encode(0, 1, 0)
    orbit = [h[seed] for h in dial]
    prepared = [tuple(orbit[(k + j) % 6] for j in (0, 1, 1, 2)) for k in range(6)]
    mixtures = [prepared[k] + prepared[k + 3] for k in range(3)]
    need(
        tuple(measure(prepared[0], detector, h) for h in dial) == TARGET, "solo fringe"
    )

    def row(g: Perm) -> tuple[int, ...]:
        return tuple(measure(s, detector, g) for s in mixtures)

    def branches(g: Perm, i: int) -> tuple[int, ...]:
        return tuple(
            int(g[dial[k][i]] in detector) + int(g[dial[k + 3][i]] in detector)
            for k in range(3)
        )

    need(all(row(h) == (4, 4, 4) for h in dial), "baseline dial exposes stock")
    swap01 = then(left, left)
    need(swap01 == tuple(encode(y, x, z) for x, y, z in TAGS), "literal wire swap")
    need(
        row(left) == (3, 2, 3) and row(right) == (4, 3, 5) and row(swap01) == (1, 2, 1),
        "frozen stock shortest and stock-independent controls",
    )
    census = Counter(row(g) for g in group)
    gaps: Counter[int] = Counter()
    for r, n in census.items():
        gaps[max(r) - min(r)] += n
        need(
            all(census[rr] == n for rr in permutations(r)),
            "permutation of mixture indices",
        )
    need(
        len(group) == 480 and gaps == {0: 96, 1: 312, 2: 72},
        "full positive-word census",
    )
    need(census[(0, 0, 0)] == 24 and census[(4, 4, 4)] == 72, "equal-setting controls")
    # Different fair three-way preparations that really *are* operationally
    # identical. This separate control supplies a trit; it is not an extra
    # random bit or an alteration to the main fair opposite-pair experiment.
    even = Counter(x for k in (0, 2, 4) for x in prepared[k])
    odd = Counter(x for k in (1, 3, 5) for x in prepared[k])
    need(even == odd == Counter({x: 2 for x in orbit}), "uniform triad equivalence")
    for u, t in product(range(1, 5), range(5)):
        change = tuple(transformed(i, u, t) for i in IDENT)
        need(
            then(change, left) == then(left, change)
            and then(change, right) == then(right, change),
            "raw affine relabeling",
        )
        changed_detector = {
            i for i in IDENT if TAGS[i][0] == t or TAGS[dial[5][i]][0] == t
        }
        need(
            {change[i] for i in detector} == changed_detector,
            "transport background reference",
        )

    # Arbitrary common nonnegative stocks. f0=1 and f3=0 force support on
    # this eligible set. There is no eligible zero-sum triple. Normalizing
    # total tag sum to 1 by an invertible scalar preserves every readout;
    # only the aggregate mass on each normalized representative matters.
    eligible = [i for i in IDENT if i in detector and dial[3][i] not in detector]
    reps = [i for i in eligible if sum(TAGS[i]) % 5 == 1]
    need(
        len(eligible) == 28
        and {transformed(i, u) for i in reps for u in range(1, 5)} == set(eligible),
        "normalized eligible orbits",
    )
    need(
        [TAGS[i] for i in reps]
        == [
            (0, 0, 1),
            (0, 1, 0),
            (0, 2, 4),
            (0, 3, 3),
            (1, 1, 4),
            (2, 4, 0),
            (3, 2, 1),
        ],
        "normalized weight order",
    )
    solo = [tuple(int(h[i] in detector) for h in dial) for i in reps]
    need(
        solo
        == [
            (1, 1, 0, 0, 1, 1),
            (1, 1, 1, 0, 0, 0),
            (1, 1, 0, 0, 0, 0),
            (1, 1, 0, 0, 0, 1),
            (1, 0, 0, 0, 0, 1),
            (1, 0, 0, 0, 1, 1),
            (1, 1, 1, 0, 0, 1),
        ],
        "linear constraints",
    )
    # Label weights x0..x6, let a=x0,c=x2. The f2,f4 equations give
    # x1+x6=x0+x5=1/4. Then f1,f5 and total give respectively
    # x0+x2+x3=x3+x4+x6=x2+x3+x4=1/2, hence x4=a, x6=c.
    # Nonnegativity gives exactly the rectangle 0<=a,c<=1/4.
    # On the original six-state orbit only reps 1,3,5 occur: a=c=0,
    # fixing precisely the original 1:2:1 probability law.
    need(set(reps) & set(orbit) == {reps[j] for j in (1, 3, 5)}, "single-orbit stock")

    def rates(g: Perm, a: F, c: F) -> tuple[F, ...]:
        weights = stock_weights(a, c)
        return tuple(
            sum(
                (
                    mass * branches(g, i)[k]
                    for mass, i in zip(weights, reps, strict=True)
                ),
                F(0),
            )
            / 2
            for k in range(3)
        )

    for a, c in product((F(0), F(1, 4)), repeat=2):
        weights = stock_weights(a, c)
        need(min(weights) >= 0 and sum(weights) == 1, "stock vertex normalization")
        need(
            all(
                sum(weights[j] * solo[j][k] for j in range(7)) == F(TARGET[k], 4)
                for k in range(6)
            ),
            "stock vertex fringe",
        )
        x, y, z = rates(swap01, a, c)
        need(x == z and y - x == F(1, 8), "wire swap all-stock vertex")
    # Proving shortest here means positive L/R contacts; inverses are not free.
    need(rates(left, F(1, 8), F(1, 8)) == (F(3, 8),) * 3, "one left mask")
    need(rates(right, F(5, 28), F(1, 7)) == (F(25, 56),) * 3, "one right mask")

    # Independent pointwise witness on ALL 125 inputs. Taking expectations
    # proves the displayed inequality for any stock without a linear solver.
    # With perfect endpoints the supported rows saturate it. A common stock
    # with |f_j-target_j|<=e has Delta>=1/8-4e, positive for e<1/32.
    minima: dict[tuple[int, int], int] = {}
    for i in IDENT:
        f = [int(h[i] in detector) for h in dial]
        counts = branches(swap01, i)
        lhs = counts[1] - counts[0]
        calibrated = -2 + 2 * f[1] + f[5]
        miss = (1 - f[0], f[3])
        need(
            lhs >= calibrated - 3 * miss[0] - 2 * miss[1], "pointwise noisy certificate"
        )
        if miss == (0, 0):
            need(lhs == calibrated, "pointwise exact certificate")
        minima[miss] = min(minima.get(miss, lhs - calibrated), lhs - calibrated)
    need(
        minima == {(0, 0): 0, (1, 0): -3, (0, 1): -2, (1, 1): -1},
        "endpoint residual minima",
    )
    print("Same four-ticket source and fair opposite branch: six old dials all 4/8.")
    print(
        "One right contact: 4,3,5 /8 (max gap 1/4). Gap counts over 480:",
        sorted(gaps.items()),
    )
    print(
        "Equal even/odd three-way controls: identical hidden stocks; no possible detector splits them."
    )
    print(
        "All 125-state nonnegative stock refits: 7 normalized eligible classes, a two-parameter rectangle."
    )
    print(
        "Swap first two wires: P(M1)-P(M0)=1/8 and P(M0)=P(M2) on the entire rectangle."
    )
    print(
        "With solo errors <=e, same-model gap >=1/8-4e. Not a measured tolerance or contextuality result."
    )


if __name__ == "__main__":
    main()
