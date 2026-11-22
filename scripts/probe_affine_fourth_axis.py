"""Pre-outcome theoretical fourth-axis cross-reference. No empirical input.

Ideal bright-probability table, counts out of four: row k=0..5 has entries
(f[k],f[k+2],f[k+4],2) cyclically, f=(4,3,1,0,1,3); the two added rows
are (2,2,2,4),(2,2,2,0). This is supplied qubit geometry (three equatorial
directions and an orthogonal fourth), not derived from the native contacts.

PRIMARY: fixed center-seed P_k, unchanged D, equatorial analyzers D after
W^0,W^2,W^4. Each new pole is a single independent native transformation
of the same four tickets; M4 is D after a common native word. Entire maps
are counted, not textual programs or experimental trials. Reversing axis
order permutes columns. Complementing all outcomes of M4 just exchanges
the two independently chosen poles. Recoding an existing column recodes
its target too; replacing its native operation is a distinct experiment.

Enumerate deterministic operations; certify optimal positive mixtures of
M4 words using integer separating inequalities and rational feasible
mixtures. The effect choice is independent of preparation. A straight
random mixture, and a mixture that may complement each effect separately,
are different classes. Also check exact escapes via source randomization,
a different common stock still giving the full solo fringe, and replacing
one old axis by a different operation indistinguishable on the old six.
These exclude a narrowly specified ideal-table implementation, not a
physical theory or empirical device. Neither qubit dimension nor an
identification of a native operation with any lab operation is given.

Run: python3 -B -O -m scripts.probe_affine_fourth_axis
"""

from collections import Counter
from fractions import Fraction as F
from itertools import permutations

from scripts.probe_affine_pulse_holdouts import (
    IDENT,
    TAGS,
    Perm,
    encode,
    gates,
    measure,
    need,
    plane_matrix,
    power,
)

Row = tuple[int, ...]
ROWS = (4, 3, 1, 0, 1, 3)
TARGET = (2, 2, 2, 2, 2, 2, 4, 0)
TRINE = (0, 2, 4)


def moves(stock: Perm, group: list[Perm]) -> list[Perm]:
    return sorted({tuple(sorted(g[i] for i in stock)) for g in group})


def score(stock: Perm, detectors: list[frozenset[int]]) -> Row:
    return tuple(sum(i in d for i in stock) for d in detectors)


def census(
    group: list[Perm],
    effects: list[frozenset[int]],
    dial: list[Perm],
    detector: frozenset[int],
    stock: Perm,
    axes: tuple[int, int, int],
) -> tuple[Counter[int], Counter[tuple[int, int, int]], list[Perm]]:
    eq = [tuple(h[i] for i in stock) for h in dial]
    stocks = moves(stock, group)
    prep_error = [
        max(abs(measure(s, detector, dial[j]) - 2) for j in axes) for s in stocks
    ]
    floor: Counter[int] = Counter()
    profiles: Counter[tuple[int, int, int]] = Counter()
    for e in effects:
        flat = max(abs(sum(i in e for i in s) - 2) for s in eq)
        values = [sum(i in e for i in s) for s in stocks]
        plus = min(max(v, 4 - y) for v, y in zip(prep_error, values, strict=True))
        minus = min(max(v, y) for v, y in zip(prep_error, values, strict=True))
        profiles[flat, plus, minus] += 1
        floor[max(flat, plus, minus)] += 1
    return (
        floor,
        profiles,
        [s for s, v in zip(stocks, prep_error, strict=True) if v == 0],
    )


# Coefficients on the six equator rates and two pole rates, in counts/4.
# For each ordered pair of exactly trine-neutral pole stocks, every
# deterministic count row r obeys c.(r-target)>=margin. Convexity preserves
# this, so maximum probability error >= margin/(4*sum(abs(c))).
STRAIGHT = {
    (0, 1): (0, 0, 8, -20, 0, 12, -14, 17),
    (0, 2): (0, -20, 8, 0, 0, 12, -14, 17),
    (1, 0): (8, 0, 0, 12, 0, -20, -14, 17),
    (1, 2): (8, -20, 0, 12, 0, 0, -14, 17),
    (2, 0): (0, 12, 0, 0, 8, -20, -14, 17),
    (2, 1): (0, 12, 0, -20, 8, 0, -14, 17),
}
SIGNED = {
    (0, 1): (-2, 0, 2, -4, 0, 4, -3, 3),
    (0, 2): (0, -4, 2, 0, -2, 4, -3, 3),
    (1, 2): (2, -4, 0, 4, -2, 0, -3, 3),
}


def bounds(rows: set[Row], coeff: Row, margin: int, expected: F) -> None:
    need(
        min(
            sum(c * (y - t) for c, y, t in zip(coeff, row, TARGET, strict=True))
            for row in rows
        )
        == margin,
        "dual bound not attained on a component",
    )
    need(F(margin, 4 * sum(map(abs, coeff))) == expected, "wrong dual normalization")


def witness(rows: set[Row], weighted: list[tuple[int, Row]], expected: F) -> None:
    den = sum(w for w, _ in weighted)
    need(all(w > 0 and r in rows for w, r in weighted), "nonphysical mixture component")
    errors = [
        abs(F(sum(w * r[i] for w, r in weighted), den) - t) / 4
        for i, t in enumerate(TARGET)
    ]
    need(max(errors) == expected, "randomized construction does not attain lower bound")


def randomized(
    eq: list[Perm], poles: list[Perm], effects: list[frozenset[int]]
) -> None:
    need(len(poles) == 3, "expected three distinct trine-neutral rotated stocks")
    need(set(STRAIGHT) == set(permutations(range(3), 2)), "straight ordered pole pairs")
    # Non-neutral poles cost >=1/4 already; identical poles cost >=1/2
    # from the opposing endpoints. Ordered pairs below exhaust the rest.
    for (i, j), coeff in STRAIGHT.items():
        inputs = eq + [poles[i], poles[j]]
        rows = {tuple(sum(x in e for x in s) for s in inputs) for e in effects}
        both = rows | {tuple(4 - y for y in r) for r in rows}
        bounds(rows, coeff, 28, F(7, 71))
        if i < j:
            bounds(both, SIGNED[i, j], 6, F(1, 12))
        # Reversing poles and globally complementing every selected effect
        # preserves errors on all six half-rate inputs for the signed model.
        if (i, j) == (1, 2):
            witness(
                rows,
                [
                    (3, (0, 0, 0, 0, 0, 0, 2, 0)),
                    (10, (0, 1, 3, 4, 3, 1, 4, 0)),
                    (4, (2, 2, 2, 2, 2, 2, 2, 0)),
                    (40, (3, 1, 1, 2, 2, 3, 4, 0)),
                    (14, (3, 4, 4, 3, 1, 1, 3, 2)),
                ],
                F(7, 71),
            )
            witness(
                both,
                [
                    (1, (1, 0, 1, 3, 4, 3, 4, 0)),
                    (3, (2, 2, 3, 3, 1, 1, 4, 0)),
                    (1, (3, 1, 1, 2, 2, 3, 4, 0)),
                    (1, (4, 3, 1, 0, 1, 3, 2, 2)),
                ],
                F(1, 12),
            )
    need(max(abs(F(1, 2) - F(t, 4)) for t in TARGET) == F(1, 2), "fair coin endpoints")


def main() -> None:
    w, group = gates()
    dial = [power(w, k) for k in range(6)]
    detector = frozenset(
        i for i in IDENT if TAGS[i][0] == 0 or TAGS[dial[5][i]][0] == 0
    )
    effects = [frozenset(i for i in IDENT if g[i] in detector) for g in group]
    seed = encode(0, 1, 0)
    stock = (seed, w[seed], w[seed], w[w[seed]])
    eq = [tuple(h[i] for i in stock) for h in dial]
    stocks = moves(stock, group)
    need(
        len(group) == 480 and len(set(effects)) == len(stocks) == 240, "native library"
    )
    target_rows = [tuple(ROWS[(k + j) % 6] for j in TRINE) + (2,) for k in range(6)]
    target_rows.extend([(2, 2, 2, 4), (2, 2, 2, 0)])
    axes = [frozenset(i for i in IDENT if dial[j][i] in detector) for j in TRINE]
    need(
        all(
            score(s, axes) == target[:3]
            for s, target in zip(eq, target_rows[:6], strict=True)
        ),
        "equator interface",
    )
    floor, profile, poles = census(group, effects, dial, detector, stock, TRINE)
    need(
        floor == {1: 84, 2: 396}
        and {k: v for k, v in profile.items() if k[0] == 0}
        == {(0, 1, 0): 6, (0, 0, 1): 6},
        "primary optimization",
    )
    need(
        census(group, effects, dial, detector, stock, (0, 4, 2))
        == (floor, profile, poles),
        "equatorial column permutation",
    )
    randomized(eq, poles, effects)

    # One signed old setting can be replaced by a *different* native map.
    # On the frozen equator they are indistinguishable, but not globally.
    alt, _, _ = census(group, effects, dial, detector, stock, (0, 1, 2))
    need(alt == {0: 8, 1: 76, 2: 396}, "native interface sensitivity")
    other = frozenset(i for i in IDENT if dial[1][i] not in detector)
    need(
        other != axes[2] and all(score(s, [other]) == score(s, [axes[2]]) for s in eq),
        "old equator does not identify the third physical setting",
    )

    # Fixed original equator and detector: keep one rotated positive pole;
    # replace only the negative pole by a fair mixture of two reachable
    # preparations. All this uses the original conserved-sum sector.
    e = next(
        e
        for g, e in zip(group, effects, strict=True)
        if plane_matrix(g) == (1, 4, 3, 0)
    )
    plus = (14, 34, 106, 106)
    minus1, minus2 = (1, 1, 22, 66), (86, 99, 123, 123)
    need(all(s in stocks for s in (plus, minus1, minus2)), "unreachable escape stock")
    need(
        all(score(s, axes + [e]) == r for s, r in zip(eq, target_rows[:6], strict=True))
        and score(plus, axes + [e]) == (2, 2, 2, 4)
        and score(minus1 + minus2, axes + [e]) == (4, 4, 4, 0),
        "positive-pole extension",
    )

    # Other exact-fringe origin: vertex a=c=1/4 in the independently
    # characterized 125-state stock rectangle. Four equally weighted
    # tickets again; all preparations, including both poles, are obtained
    # from this ONE common source by individual native transformations.
    other_stock = tuple(
        encode(*t) for t in ((0, 0, 1), (0, 2, 4), (1, 1, 4), (3, 2, 1))
    )
    need(
        tuple(measure(other_stock, detector, h) for h in dial) == ROWS,
        "alternate common fringe",
    )
    other_eq = [tuple(h[i] for i in other_stock) for h in dial]
    other_moves = moves(other_stock, group)
    new_effect = next(
        e
        for g, e in zip(group, effects, strict=True)
        if plane_matrix(g) == (4, 2, 1, 4)
    )
    new_plus, new_minus = (1, 42, 90, 102), (22, 34, 82, 123)
    need(
        new_plus in other_moves
        and new_minus in other_moves
        and [score(s, axes + [new_effect]) for s in other_eq + [new_plus, new_minus]]
        == target_rows,
        "alternate common-source whole ideal witness",
    )
    print("Ideal counts/4, rows 0..5,+,- and columns W^0,W^2,W^4,M4:", target_rows)
    print(
        "Fixed original four-ticket stock: no deterministic exact hit; minimax error 1/4 (84/480)."
    )
    print(
        "Random native analyzer: minimax 7/71 straight, 1/12 with per-component complements."
    )
    print(
        "Separate 0,1,2 physical interface: 8/480 complete exact hits; old equator cannot tell them apart."
    )
    print(
        "A fair mixture for one new pole, or a different common four-ticket origin, permits an exact ideal."
    )
    print("No empirical inputs, uncertainties or physical setting identification.")


if __name__ == "__main__":
    main()
