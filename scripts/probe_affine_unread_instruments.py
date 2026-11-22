"""Sequential holdout on the frozen F5 six-state code, with the first bit kept.

The comparison is the *supplied* rank-one, repeatable projective qubit
instrument on the six calibrated equatorial directions, with no evolution
besides the stated analyzer change. This is not derived from solo rates:
a different physical instrument with the very same first-click probabilities
can disturb the system differently. All joint probabilities include every
input ticket; conditional probabilities use only the named first outcome.

We distinguish a nondisturbing classical copy, an independent fair native
reflection, arbitrary doubly stochastic postchannels on the six states,
and a reversible reset with a consumed three-valued source. The reset is
an abstract dilation, NOT a program of the affine color contact. The finite
affine obstruction assumes that each realized poststate lies on the original
six-state code and that the external control does not branch on a read bit.
No conclusion about all hidden spaces, quantum theory or experiments.

Replay: python3 -B -O -m scripts.probe_affine_unread_instruments
"""

from collections import Counter
from fractions import Fraction as F
from itertools import combinations, product

from scripts.probe_affine_pulse_holdouts import FRINGE, TAGS, encode, gates, need, power

Kernel = tuple[tuple[F, ...], ...]
S = range(6)
PREP = tuple(tuple(F((0, 1, 1, 2).count((t - n) % 6), 4) for t in S) for n in S)
IDEAL = tuple(F(x, 4) for x in FRINGE)


def click(t: int, dial: int = 0) -> bool:
    return (t + dial) % 6 < 3


def joint(k: Kernel, n: int, a: bool, j: int) -> F:
    """Probability of first outcome a AND a bright second result."""
    return sum(
        (PREP[n][t] * k[t][v] for t in S if click(t) == a for v in S if click(v, j)),
        F(0),
    )


def target(n: int, a: bool, j: int) -> F:
    mass = IDEAL[n] if a else 1 - IDEAL[n]
    return mass * IDEAL[(j + (0 if a else 3)) % 6]


def max_error(k: Kernel, *, conditional: bool = False) -> F:
    return max(
        abs(joint(k, n, a, j) - target(n, a, j)) / (mass if conditional else 1)
        for n, j, a in product(S, S, (True, False))
        if (mass := (IDEAL[n] if a else 1 - IDEAL[n]))
    )


def rank_three(rows: list[tuple[F, ...]]) -> bool:
    for u, v, w in combinations(rows, 3):
        if (
            u[0] * (v[1] * w[2] - w[1] * v[2])
            - u[1] * (v[0] * w[2] - w[0] * v[2])
            + u[2] * (v[0] * w[1] - w[0] * v[1])
        ):
            return True
    return False


def main() -> None:
    w, group = gates()
    orbit = [power(w, j)[encode(0, 1, 0)] for j in S]
    inverse = power(w, 5)
    need(
        [TAGS[i][0] == 0 or TAGS[inverse[i]][0] == 0 for i in orbit]
        == [click(t) for t in S],
        "actual terminal reader differs",
    )
    need(tuple(sum(row[:3], F(0)) for row in PREP) == IDEAL, "solo calibration")
    reflect = [g for g in group if all(g[orbit[t]] == orbit[(2 - t) % 6] for t in S)]
    need(len(reflect) == 1, "missing/ambiguous raw pulse for sector reflection")
    copy = tuple(tuple(F(t == v) for v in S) for t in S)
    coin = tuple(tuple((F(t == v) + F((2 - t) % 6 == v)) / 2 for v in S) for t in S)
    uniform = tuple(tuple(F(click(t) == click(v), 3) for v in S) for t in S)
    reset = tuple(PREP[0 if click(t) else 3] for t in S)
    need(
        all(
            sum(row, F(0)) == 1 and min(row) >= 0
            for k in (copy, coin, uniform, reset)
            for row in k
        )
        and all(sum(k[t][v] for t in S) == 1 for k in (copy, coin, uniform) for v in S),
        "channels not normalized",
    )
    need(
        [sum(reset[t][v] for t in S) for v in S] == [F(3, 4), F(3, 2), F(3, 4)] * 2,
        "reset would be unital",
    )

    def unread(k: Kernel, n: int, j: int) -> F:
        return joint(k, n, True, j) + joint(k, n, False, j)

    need(
        unread(copy, 2, 4) == 1 and unread(reset, 2, 4) == F(5, 8),
        "intermediate read control",
    )
    need(
        all(unread(coin, n, j) == unread(reset, n, j) for n, j in product(S, repeat=2)),
        "blind marginals",
    )
    need(
        joint(coin, 2, True, 2) == F(1, 8) and target(2, True, 2) == F(1, 16),
        "first-bit holdout",
    )
    need(
        all(
            joint(coin, n, True, 0) == IDEAL[n] and not joint(coin, n, False, 0)
            for n in S
        ),
        "repeatability",
    )

    # Exact minimax JOINT error. For first-bright branches of P1 and P5,
    # total input weights per state are (1/2,1/2,1/2,0,0,0).
    # The difference of second effects E5-E4 is the point mass at 1 minus
    # the point mass at 4. Thus the sum of both joint differences is <=1/2
    # by column capacity, for every positive doubly stochastic K, repeatable
    # or not. Target 3/4: four entries cannot all miss by less than 1/16.
    need(
        [sum(PREP[n][t] for n in (1, 5)) * click(t) for t in S]
        == [F(1, 2)] * 3 + [0] * 3,
        "dual source",
    )
    need(
        [int(click(t, 5)) - int(click(t, 4)) for t in S] == [0, 1, 0, 0, -1, 0],
        "dual effect",
    )
    need(
        sum(target(n, True, 5) - target(n, True, 4) for n in (1, 5)) == F(3, 4),
        "dual target",
    )
    need(
        max_error(coin) == F(1, 16),
        "native random pulse does not attain sharp joint bound",
    )
    # CONDITIONAL minimax: uniformly mixing the six P_n gives uniform raw
    # input. After first bright, each post-atom has mass <=1/3 by the same
    # capacity. The average bright rate of E1 and E5 is
    # (1+mass(1)-mass(4))/2 <=2/3, versus 3/4 for the projective branch.
    need(
        [sum(PREP[n][t] for n in S) for t in S] == [1] * 6, "uniform calibration stock"
    )
    need(
        [int(click(t, 1)) + int(click(t, 5)) for t in S] == [1, 2, 1, 1, 0, 1],
        "conditional dual",
    )
    need(
        max_error(uniform, conditional=True) == F(1, 12),
        "sharp conditional upper witness",
    )

    # Exact sequential data uniquely fixes the six-by-six raw kernel.
    # Positive repeatability forbids cross-sector entries (each input occurs
    # with nonzero mass). In each remaining three-by-three block, the measured
    # joint matrix is B K E. Both preparation and analyzer restrictions have
    # column rank three, so B K E is injective in K on that block.
    for side in (0, 3):
        sector = range(side, side + 3)
        need(rank_three([tuple(row[t] for t in sector) for row in PREP]), "source rank")
        need(
            rank_three([tuple(F(click(t, j)) for t in sector) for j in S]),
            "effect rank",
        )
    need(max_error(reset) == 0, "reset does not realize the sequential benchmark")
    # Reversible dilation on six states times three labels. Fresh helper
    # distribution is 1:2:1; its outgoing label exports the old within-sector
    # coordinate. Two support points alone cannot supply three outputs for a
    # fixed input under any deterministic dilation.
    outputs = {(3 * (t // 3) + r, t % 3) for t, r in product(S, range(3))}
    need(len(outputs) == 18, "dilation not invertible")
    need(
        all(sum(u > 0 for u in row) == 3 for row in reset), "helper support lower bound"
    )
    need(
        all(
            reset[t][v]
            == sum(
                (F((1, 2, 1)[r], 4) for r in range(3) if 3 * (t // 3) + r == v), F(0)
            )
            for t, v in product(S, repeat=2)
        ),
        "dilation marginal",
    )

    # Enumerate all affine restrictions of ANY fixed-address affine color
    # circuit (enlarged with fixed helpers) that returns its six inputs to
    # this same code. The six span their constant-sum plane. If all six
    # outputs lie on it, their x,y coordinates determine the whole map.
    points = [TAGS[i][:2] for i in orbit]
    counts: Counter[tuple[int, bool]] = Counter()
    for a, b, c, d, e, f in product(range(5), repeat=6):
        image = [((a * x + b * y + e) % 5, (c * x + d * y + f) % 5) for x, y in points]
        if all(p in points for p in image):
            perm = [points.index(p) for p in image]
            counts[len(set(perm)), all(click(t) == click(perm[t]) for t in S)] += 1
    need(counts == {(1, False): 6, (6, False): 10, (6, True): 2}, "affine code census")
    # A repeatable positive mixture can use only sector-preserving maps;
    # constants cannot make both outcomes repeat. Of the affine superspace
    # only identity/reflection remain, each available natively.
    print(
        "Clean copy: unread 1 vs 5/8. Native fair reflection: all 36 unread rates match; joint 1/8 vs 1/16."
    )
    print(
        "Six-state doubly stochastic postchannels: sharp worst-case joint gap 1/16; conditional gap 1/12."
    )
    print(
        "Exact sequential target uniquely requires sector reset. Reversible abstract dilation uses 3-valued fresh stock."
    )
    print(
        "15,625 affine plane maps: 6 constants and 12 permutations preserve the hexagon; only 2 repeat the recorded bit."
    )


if __name__ == "__main__":
    main()
