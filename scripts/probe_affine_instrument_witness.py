"""A noise-tolerant three-probability test of the affine postchannel.

Use the archived source/first reader, uniformly mix P0,P2,P4, and keep
both outcomes. The postchannel is any mixture of affine maps independent
of the current signal. Second settings are just the original reader at
zero and the same reader after ONE right contact R. Neither exact endpoint
probabilities, a six-state output, nor access to individual hidden phases
is required for the resulting inequality. The certified input preparation,
first reader, allowed schedules and independent source are still essential.
This is a design, not a tested laboratory inequality against nature.
"""

from fractions import Fraction as F
from itertools import product
from math import comb

from scripts.probe_affine_pulse_holdouts import (
    IDENT,
    TAGS,
    contacts,
    encode,
    need,
    power,
)
from scripts.probe_affine_reset_escape import branches

Triple = tuple[int, int, int]


def win(p: F, q: F, r: F) -> F:
    """Endpoint bright|bright, right bright|bright, endpoint bright|dark."""
    return F(1, 2) + (3 * p + 3 * q - r) / 12


def tail(n: int, k: int, p: F) -> F:
    """Exact and short upper tail for a binary, fixed-N design."""
    a, b = p.numerator, p.denominator - p.numerator
    return F(
        sum(comb(n, i) * a**i * b ** (n - i) for i in range(k, n + 1)), p.denominator**n
    )


def main() -> None:
    orbit, ds, d = branches()
    _, right = contacts()
    shared = {i for i in IDENT if i in d and right[i] in d}
    need(
        shared == {i for i in IDENT if TAGS[i][0] == 0},
        "the two bright tests do not meet in the input-coordinate plane",
    )
    first = [encode(*x) for x in orbit]
    need([i in d for i in first] == [True] * 3 + [False] * 3, "first record code")
    # The first three raw states affinely span the six-input plane. The
    # image of their affine span under ANY affine map is contained in
    # the affine span of their images. Check explicitly on the 25 points.
    u, v, w = orbit[:3]
    plane = {
        tuple(((1 - h - k) * u[j] + h * v[j] + k * w[j]) % 5 for j in range(3))
        for h, k in product(range(5), repeat=2)
    }
    need(len(plane) == 25 and set(orbit) <= plane, "first three states do not span")
    # For each deterministic postmap let i,r be bright second counts
    # on the three first-bright states at settings zero,R; j the count at
    # zero on the other three. If i+r<=5, 3i+3r-j<=15 immediately.
    # If i=r=3, all three images lie in shared={x=0}; by affinity all
    # six lie there. Thus j=3. No test at the old antipodal dial needed.
    need(
        max(
            3 * i + 3 * r - j
            for i, r, j in product(range(4), repeat=3)
            if (i, r) != (3, 3) or j == 3
        )
        == 15,
        "count bound",
    )
    # P0,P2,P4 contribute two tickets per hidden phase. This is why an
    # inequality on three-state counts becomes an observed-probability
    # inequality even without access to a particular individual phase.
    need(
        [sum((0, 1, 1, 2).count((t - k) % 6) for k in (0, 2, 4)) for t in range(6)]
        == [2] * 6,
        "unbalanced first branches",
    )
    # Exact sharp Chebyshev distance on the THREE named conditional rates.
    # Ideal functional =21/4 vs ceiling 5 and coefficient norm 7 => 1/28.
    # The witness of tightness is a fair-independent 28-ticket *design*
    # (not a bit with 28 equally likely outputs). It mixes identity, R^-1,
    # or emitting three fresh blanks; data can swap onto scratch in the
    # last branch. Each is a native fixed-address program with blanks.
    ideal = (F(1), F(3, 4), F(0))
    rows = []
    for g in (IDENT, power(right, 3), (0,) * 125):
        after = [g[i] for i in first]
        rows.append(
            (
                sum(i in d for i in after[:3]),
                sum(right[i] in d for i in after[:3]),
                sum(i in d for i in after[3:]),
            )
        )
    need(rows == [(3, 2, 0), (2, 3, 0), (3, 3, 3)], "three positive maps")
    witness = tuple(
        sum(
            (
                F(weight * row[k], 84)
                for weight, row in zip((24, 3, 1), rows, strict=True)
            ),
            F(0),
        )
        for k in range(3)
    )
    need(
        tuple(abs(p - q) for p, q in zip(witness, ideal, strict=True))
        == (F(1, 28),) * 3,
        "sharp upper witness",
    )
    need(
        3 * ideal[0] + 3 * ideal[1] - ideal[2] == F(21, 4)
        and 3 * witness[0] + 3 * witness[1] - witness[2] == 5,
        "dual witness",
    )
    # Assess the requested conditional outgoing preparations with the ACTUAL
    # D,R. For frozen P0 the R-bright probability is 3/4. This does not
    # assign R an observed quantum angle. For a nonlinear control map that
    # sees the bit, P0/P3 is a possible reset, demonstrating scope.
    p0 = (first[0], first[1], first[1], first[2])
    p3 = (first[3], first[4], first[4], first[5])
    need(
        (
            sum(i in d for i in p0),
            sum(right[i] in d for i in p0),
            sum(i in d for i in p3),
        )
        == (4, 3, 0),
        "instrument target",
    )
    need(ds[0] == IDENT, "zero analyzer changed")

    # Binary trial game: commit output before the second setting/reward
    # ticket is available. After first bright choose 0 or R by a fresh fair
    # bit, score a second bright. After first dark use 0; a dark second
    # always wins, and a bright second wins on five of six independent
    # reward tickets. Every trial gets a binary score, no postselection.
    # P(first bright)=1/2 is a source premise, not estimated by dividing
    # noisy totals. Half+functional/12 is the unconditional win rate.
    null_q, alt_q = F(11, 12), F(15, 16)
    need(win(*ideal) == alt_q and win(*witness) == null_q, "game endpoints")
    for i, r, j in rows:
        hits = 0
        for t, setting, lot in product(range(6), range(2), range(6)):
            hits += int(
                (t < (i if setting == 0 else r)) if t < 3 else (t - 3 >= j or lot < 5)
            )
        need(F(hits, 72) == win(F(i, 3), F(r, 3), F(j, 3)), "binary payoff")
    # The idealized IID alternative is only for *power*. The fixed-N null
    # tail remains conservative for arbitrary past history if every trial
    # has this conditional win cap. The game must not adapt n or select
    # among already observed protocols using this threshold.
    n, k = 1500, 1393
    a, power_at_target = tail(n, k, null_q), tail(n, k, alt_q)
    need(
        a <= F(1, 20) < tail(n, k - 1, null_q)
        and F(926, 1000) < power_at_target < F(927, 1000),
        "prospective fixed-N design",
    )
    # If the joint pre-setting draw of hidden input and schedule conditional
    # on past history is within TV eta of the stipulated independent law,
    # a [0,1] game score can move by at most eta. Or if a conditional
    # fraction kappa is arbitrary contamination, q <= (1-kappa)q0+kappa.
    # These are two different source contracts. No noise budget is certified.
    need(
        alt_q - null_q == F(1, 48) and (alt_q - null_q) / (1 - null_q) == F(1, 4),
        "noise margins",
    )
    print(
        "Three observed rates p=bright|first bright at zero, q=bright|first bright after R, r=bright|first dark at zero: 3p+3q-r <= 5."
    )
    print(
        "Target (1,3/4,0) gives 21/4. Sharp L-infinity distance to affine mixtures on these three rates: 1/28, no perfect-repeat assumption."
    )
    print(
        "All-trial game: affine cap 11/12, supplied reset 15/16. Example: >=1393 of 1500 wins; "
        f"fixed-N null tail {float(a):.6f}, IID target power {float(power_at_target):.6f}."
    )
    print(
        "Certified input interface, fresh setting/reward and affine stock independence are assumptions; design only, no observed rejection."
    )


if __name__ == "__main__":
    main()
