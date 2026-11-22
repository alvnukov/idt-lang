"""Two pulse settings, one unchanged four-ticket source and one terminal detector.

Two equal 60-degree equatorial rotations of relative azimuth delta form the
SUPPLIED comparison family, not a law of the six marks. The isolated z-return
fringe cannot identify delta. Write c=cos(delta); chronology is left to right,
lowercase means the inverse of the *entire* corresponding pulse. No detector
is applied between letters. Two alternative calibration protocols are:

1. Freeze q=p(Ab). In the rotation model c=(8q-5)/3, p(AB)=5/4-q.
   If a=(3-c)/4 is the scalar part of the AB unit quaternion, squaring it
   multiplies the transverse vector by 2a, so p(ABAB)=1-4a²(1-p(AB)).
   Interior on-grid q=1/2,3/4 give second holdouts 11/36,1/9. The first
   holdout is on the quarter grid in BOTH cases. Neither sign of delta has
   to be chosen. Around q=3/4+t the second holdout equals
   1/9+(8/3)t²-(16/9)t³. For |t|<=1/12 it lies in [1/9,127/972],
   inside [1/9,5/36], so its distance to every quarter is STILL >=1/9.
   This is a calibration tolerance, not an observed confidence interval.
   Do not refit the angle, preparation, detector or pulses.
2. Use C=ABBBa INSTEAD of Ab. In the rotation model its return equals the
   squared projection of the A-tilted pole onto the B axis: 3(1-c²)/4.
   C=3/4 thus nominates quadrature; both handednesses predict AB=5/8 and
   ABAB=5/32. If C is only known to be >=3/4-e, the ideal family gives
   |p(AB)-5/8| <= (3/8)sqrt(4e/3). The four-ticket gap stays positive
   when e<1/12, before any error in AB. Conflicting calibrations are evidence
   against the comparison family, not license to pick one after looking.

For quadrature the AB return is the OLD centered trace (4+3 cos(n phi))/7,
cos(phi)=1/8; see probe_native_markov_spectrum.py for its homogeneous-kernel
obstructions. Here its denominator prices a different resource: for n>=1,
it is 2^(2n+1) in lowest terms. This follows from p0=1,p1=5/8 and
p[n+1]=1+p[n]/4-p[n-1]: on the next denominator the middle numerator is
odd, the other terms even. This costs at least 2n+1 fixed fair source bits
with deterministic routes and binary terminal readout, not 2n+1 measured
bits, or that many bits of persistent state in an arbitrary stochastic model.

The census starts with frozen families and checks ALL single-axis lengths
before the mixed words. 1:2:1 is literally the same joint state stock for
both settings. The unrestricted six-label permutations are countercontrols,
not derived scatterers; named examples are witnesses from the census, not
independently nominated physical devices. Changing a port label on paper is
not actuation. The rotation formulas, fair preparation, actuator access,
fixed incidence and absence of loss are assumptions. No empirical pulse,
noise estimate, source of probabilities, spatial axes or universal primitive
exclusion follows. New random transitions, extra shared randomness, moving
detectors or unequal ticket weights can evade the quarter grid; one fixed
finite homogeneous Markov kernel is a different, separately bounded family.

Run: python3 -B -O -m scripts.probe_phase_pair_holdout
"""

from collections import Counter
from fractions import Fraction as F
from itertools import permutations, product
from math import lcm

from scripts.probe_opposition_clock_scatter import FLAGS, extend
from scripts.probe_three_opposition_origin import WORDS

FRINGE = (4, 3, 1, 0, 1, 3)
WORDS_TO_READ = ("Ab", "AB", "ABAB", "ABBBa")
Perm = tuple[int, ...]


def need(ok: bool, message: str) -> None:
    if not ok:
        raise ArithmeticError(message)


def rotation_return(word: str, c: F) -> F:
    """Independent Rodrigues walk. Horizontal coordinates use A×z and B×z,
    in units of 1/sqrt(3); their Gram off-diagonal is c. This also works
    when this spanning set is dependent (c=±1). Only exact rationals enter.
    """
    need(-1 <= c <= 1, "relative cosine out of range")
    x, y, z = F(0), F(0), F(1)
    for letter in word:
        need(letter in "AaBb", "unrecognized pulse")
        use_b = letter.upper() == "B"
        if use_b:
            x, y = y, x
        sign = 1 if letter.isupper() else -1
        h = x + c * y
        x, z = x + (3 * sign * z - h) / 2, (z - sign * h) / 2
        if use_b:
            x, y = y, x
        need(z * z + (x * x + y * y + 2 * c * x * y) / 3 == 1, "rotation lost norm")
    return (1 + z) / 2


def inverse_calibration(q: F) -> tuple[F, F, F]:
    c = (8 * q - 5) / 3
    need(-1 <= c <= 1, "inverse-command calibration outside comparison family")
    first = F(5, 4) - q
    second = 1 - 4 * ((3 - c) / 4) ** 2 * (1 - first)
    return c, first, second


def quarter_gap(p: F) -> F:
    return min(abs(p - F(k, 4)) for k in range(5))


def benchmark() -> None:
    for c in (F(-1), F(-1, 3), F(0), F(1, 3), F(1)):
        q, first, second, half_turn = (rotation_return(w, c) for w in WORDS_TO_READ)
        need(inverse_calibration(q) == (c, first, second), "two-pulse predictions")
        need(half_turn == 3 * (1 - c * c) / 4, "conjugate half-turn calibration")
        for letter in "AB":
            need(
                tuple(4 * rotation_return(letter * n, c) for n in range(6))
                == tuple(map(F, FRINGE)),
                "an isolated pulse reveals the azimuth",
            )
    for q, first, second, gap in (
        (F(1, 2), F(3, 4), F(11, 36), F(1, 18)),
        (F(3, 4), F(1, 2), F(1, 9), F(1, 9)),
    ):
        need(
            inverse_calibration(q)[1:] == (first, second)
            and quarter_gap(second) == gap,
            "on-grid first, off-grid second",
        )
    e = F(1, 12)
    # For |t|<=e, t²(8/3-16t/9) lies between zero and this endpoint shift.
    upper = F(1, 9) + e**2 * (F(8, 3) + 16 * e / 9)
    need(
        upper == inverse_calibration(F(3, 4) - e)[2] == F(127, 972)
        and upper <= F(5, 36),
        "toleranced inverse calibration",
    )
    prev, cur = F(1), F(5, 8)
    for n in range(1, 33):
        need(
            rotation_return("AB" * n, F(0)) == cur
            and cur.denominator == 2 ** (2 * n + 1),
            "quadrature recurrence/denominator",
        )
        prev, cur = cur, 1 + cur / 4 - prev
    need(rotation_return("ABAB", F(0)) == F(5, 32), "quadrature second holdout")


def inverse(g: Perm) -> Perm:
    return tuple(g.index(i) for i in range(len(g)))


def period(g: Perm) -> int:
    ident = tuple(range(len(g)))
    need(tuple(sorted(g)) == ident, "not a permutation")
    p, n = g, 1
    while p != ident:
        p, n = tuple(g[i] for i in p), n + 1
    return n


def advance(stock: Perm, pulse: Perm) -> Perm:
    return tuple(pulse[i] for i in stock)


def single_axis(stock: Perm, bright: frozenset[int], pulse: Perm, order: int) -> bool:
    for n in range(lcm(order, len(FRINGE))):
        if sum(i in bright for i in stock) != FRINGE[n % 6]:
            return False
        stock = advance(stock, pulse)
    return True


def mixed(stock: Perm, bright: frozenset[int], a: Perm, b: Perm) -> tuple[int, ...]:
    pulses = {"A": a, "B": b, "a": inverse(a), "b": inverse(b)}
    out = []
    for word in WORDS_TO_READ:
        tickets = stock
        for letter in word:
            tickets = advance(tickets, pulses[letter])
        out.append(sum(i in bright for i in tickets))
    return tuple(out)


def shuttle_census() -> Counter[tuple[int, ...]]:
    gates = sorted({extend(u, v, False) for u, v in FLAGS})
    # Physical state: 6*station+mark. A station advances only on a pulse.
    library = [tuple(6 + i for i in g0) + g1 for g0, g1 in product(gates, repeat=2)]
    orders = [period(g) for g in library]
    need(len(gates) == 6 and Counter(orders) == {2: 6, 4: 6, 6: 24}, "shuttle library")
    joint_detectors = [frozenset(i for i in range(12) if i % 6 in d) for d in WORDS]
    kept = 0
    outcomes: Counter[tuple[int, ...]] = Counter()
    for a, na in zip(library, orders, strict=True):
        for seed, bright in product(range(6), joint_detectors):
            stock = (seed, a[seed], a[seed], a[a[seed]])
            if not single_axis(stock, bright, a, na):
                continue
            kept += 1
            for b, nb in zip(library, orders, strict=True):
                if single_axis(stock, bright, b, nb):
                    need(b in (a, inverse(a)), "genuinely new shuttle orientation")
                    outcomes[mixed(stock, bright, a, b)] += 1
    need(
        kept == 96 and outcomes == {(1, 4, 4, 0): 96, (4, 1, 1, 0): 96},
        "same-stock native shuttle census",
    )
    return outcomes


def six_mark_controls() -> Counter[tuple[int, ...]]:
    # Label by position on the supplied A orbit; opposition is i -> i+3 mod 6.
    # This index is not identified with the numeric opposition labels above.
    a = (1, 2, 3, 4, 5, 0)
    stock, bright = (0, 1, 1, 2), frozenset((0, 1, 2))
    outcomes: Counter[tuple[int, ...]] = Counter()
    symmetric: list[Perm] = []
    survivors: dict[Perm, tuple[int, ...]] = {}
    for b in permutations(range(6)):
        if single_axis(stock, bright, b, period(b)):
            row = mixed(stock, bright, a, b)
            outcomes[row] += 1
            survivors[b] = row
            if all(b[(i + 3) % 6] == (b[i] + 3) % 6 for i in range(6)):
                symmetric.append(b)
    need(
        sum(outcomes.values()) == 12 and set(symmetric) == {a, inverse(a)},
        "single-axis-equivalent six-mark alternatives",
    )
    # Both pass their respective Ab calibration and first mixed holdout;
    # the second misses. BOTH pass C=3/4 in the *separate* quadrature protocol.
    need(
        survivors[(3, 0, 1, 4, 5, 2)] == (2, 3, 4, 3)
        and survivors[(1, 2, 4, 0, 5, 3)] == (3, 2, 2, 3),
        "interior witnesses",
    )
    need(
        sum(n for r, n in outcomes.items() if r[3] == 3) == 4,
        "number reaching standalone quadrature calibration",
    )
    return outcomes


def main() -> None:
    benchmark()
    shuttle, controls = shuttle_census(), six_mark_controls()
    print("Two alternative calibrations of a supplied 60-degree rotation benchmark.")
    print(
        "Ab=1/2 -> AB=3/4, ABAB=11/36 (quarter-gap 1/18); "
        "Ab=3/4 -> AB=1/2, ABAB=1/9 (quarter-gap >=1/9 even for |Ab-3/4|<=1/12)."
    )
    print(
        "ABBBa=3/4 -> AB=5/8 (quarter-gap 1/8), ABAB=5/32; "
        "depth n>=1 needs >=2n+1 fixed fair ticket bits for an exact deterministic fit."
    )
    print(
        "Readout counts out of four for (Ab,AB,ABAB,ABBBa); tagged tuple multiplicities:"
    )
    print(
        "Transparent two-station shuttles: 96 source/setting/detector triples, "
        "192 ordered pairs; only identical/inverse complete maps:",
        sorted(shuttle.items()),
    )
    print(
        "Unrestricted second six-mark permutations: 12/720 pass both solo fringes; "
        "only A and inverse(A) preserve opposition:",
        sorted(controls.items()),
    )
    print(
        "No independently calibrated second orientation in these shuttles. Other "
        "six-mark controls reach interior calibrations and fail the mixed prediction. "
        "No physical exclusion or stochastic-kernel claim from four-ticket counting."
    )


if __name__ == "__main__":
    main()
