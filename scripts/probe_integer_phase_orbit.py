"""Exact two-port holdout for a balanced integer phase shifter.

The fixed recipe is H, then k copies of diag(2-i, 2+i), then H and
the unchanged detector grouping ((0, 1), (2, 3)). Every gate acts on the
unnormalized signed integer cloud. H, event routing and cancellation are
supplied by the frozen parent fixture, not derived here.
After dividing by the common amplitude scale, the left arm is a unit
complex common phase multiplying diag(1, z). It is not an identity arm.

For k = 0, 1, 2 both explicit ticket matchings are exercised. All depths
0..128 also use compressed exact counts: the squared signed rail totals
count ordered survivor pairs, including repeated IDs. These counts are not
enumerations of individual trajectories at large depth.

The fixed calibration target is the unit complex number (5+12i)/13, not
selected from the measured orbit. Chord distance sees both quadratures;
the detector only measures the real-part projection. Neither is refitted.
The target is non-Clifford as a conventional relative phase: it is not a
quarter turn or any integer multiple of one.

Arithmetic behind the scope: if n = a+bi and a²+b² = p², then n² = 2a*n
modulo p, so n^k = (2a)^(k-1)*n modulo p. At (a,b,p) = (3,4,5) and
(5,12,13), p divides neither 2a nor b. Thus z = (3+4i)/5 and the target
both have irrational angles in turns (no positive power is real). A finite
orbit point cannot hit the target because its real part has denominator
dividing 5^k, while 5/13 is reduced. Analytic density assumes indefinitely
available repeated gates: pigeonholing powers of an irrational rotation
gives arbitrarily small nonzero angular steps, whose successive multiples
approximate a full turn. That argument gives neither exact continuous
settings nor a finite-energy, finite-depth or physical shifter claim.

Run from the repository root: python3 -O -m scripts.probe_integer_phase_orbit
"""

import sys
from fractions import Fraction
from hashlib import sha256
from math import isqrt
from pathlib import Path

if not __package__:
    sys.path.insert(0, str(Path(__file__).resolve().parents[1]))

from scripts.probe_cancellation_event_router import Cloud, H, Matrix, dot, need, run

Gaussian = tuple[int, int]
Counts = tuple[int, int]
Phase = tuple[Fraction, Fraction]
ROUTER_SHA256 = "3ea92c7f3e9092989166492b990b0be30c9c9e1a8689c41d1fc1700742da1b66"
Z_NUM = (3, 4)
Z_DEN = 5
TARGET_NUM = (5, 12)
TARGET_DEN = 13
TARGET = (Fraction(TARGET_NUM[0], TARGET_DEN), Fraction(TARGET_NUM[1], TARGET_DEN))
WINDOWS = (8, 16, 32, 64, 128)
IDENTITY = (Fraction(1), Fraction(0))
UNITS = {(-1, 0), (0, -1), (0, 1), (1, 0)}


def gaussian_mul(left: Gaussian, right: Gaussian) -> Gaussian:
    a, b = left
    c, d = right
    return a * c - b * d, a * d + b * c


def two_arm(left: Gaussian, right: Gaussian) -> Matrix:
    a, b = left
    c, d = right
    return ((a, -b, 0, 0), (b, a, 0, 0), (0, 0, c, -d), (0, 0, d, c))


def gain_matches(gate: Matrix, gain: int) -> bool:
    cols = tuple(zip(*gate, strict=True))
    return all(
        dot(col, other) == (gain if i == j else 0)
        for i, col in enumerate(cols)
        for j, other in enumerate(cols)
    )


def apply(gate: Matrix, state: tuple[int, ...]) -> tuple[int, ...]:
    return tuple(dot(row, state) for row in gate)


def counts_by_port(rail_counts: tuple[int, ...]) -> Counts:
    a, b, c, d = rail_counts
    need(min(rail_counts) >= 0, "negative raw count")
    return a + b, c + d


def check_minimal_gaussian_pair() -> None:
    """Exhaust the equal-norm two-Gaussian-multiplier family through gain 5."""
    for gain, population in enumerate((4, 4, 0, 4, 8), start=1):
        box = range(-isqrt(gain), isqrt(gain) + 1)
        multipliers = [(a, b) for a in box for b in box if a * a + b * b == gain]
        numerators = {
            gaussian_mul((a, -b), right)
            for a, b in multipliers
            for right in multipliers
        }
        unit_numerators = {(a * gain, b * gain) for a, b in UNITS}
        need(len(multipliers) == population, f"wrong norm-{gain} Gaussian population")
        if gain < Z_DEN:
            need(numerators <= unit_numerators, f"smaller gain {gain} is not torsion")
        else:
            need(
                Z_NUM in numerators - unit_numerators,
                "gain five misses the nonunit relative phase",
            )
    for (a, b), p in ((Z_NUM, Z_DEN), (TARGET_NUM, TARGET_DEN)):
        need(a * a + b * b == p * p, "phase does not have unit norm")
        need(Fraction(2 * a, p).denominator == p, "real component not coprime")
        need(Fraction(b, p).denominator == p, "imaginary component not coprime")


def chord_squared(point: Phase, target: Phase) -> Fraction:
    x, y = point
    u, v = target
    return 2 * (1 - x * u - y * v)


def bracket(value: Fraction) -> str:
    """Outward decimal brackets computed in integers, not rounded float values."""
    scale = 10**9
    lower = value.numerator * scale // value.denominator
    upper = lower + 1
    return (
        f"[{lower // scale}.{lower % scale:09d}, {upper // scale}.{upper % scale:09d})"
    )


def main() -> None:
    router = Path(__file__).with_name("probe_cancellation_event_router.py")
    need(
        sha256(router.read_bytes()).hexdigest() == ROUTER_SHA256,
        "parent router changed",
    )

    check_minimal_gaussian_pair()
    shifter = two_arm((2, -1), (2, 1))
    bare_bypass = two_arm((1, 0), (2, 1))
    padded_bypass = two_arm((5, 0), Z_NUM)
    need(gain_matches(H, 4), "frozen H not balanced")
    need(gain_matches(shifter, Z_DEN), "gain-five shifter not balanced")
    need(not gain_matches(bare_bypass, 1), "unscaled identity bypass accepted")
    need(gain_matches(padded_bypass, Z_DEN**2), "gain-25 bypass not balanced")

    initial_cloud: Cloud = ((0, 1),)
    initial_state = (1, 0, 0, 0)
    state = padded_state = apply(H, initial_state)
    num = (1, 0)
    den = 1
    total = padded_total = 4 * 4
    phase_orbit: list[Phase] = []
    raw_counts: list[Counts] = []
    for k in range(WINDOWS[-1] + 1):
        x, y = num
        phase = (Fraction(x, den), Fraction(y, den))
        need(x * x + y * y == den * den, f"phase drift at k={k}")
        if k:
            need((x % Z_DEN, y % Z_DEN) == Z_NUM, f"mod-five residue at k={k}")
        phase_orbit.append(phase)

        # These are computed from the raw integer matrix action, before
        # comparison to the independent complex relative-phase oracle.
        detected = apply(H, state)
        rail_counts = tuple(a * a for a in detected)
        port_counts = counts_by_port(rail_counts)
        need(sum(port_counts) == total == 16 * Z_DEN**k, f"lost events at k={k}")
        need(k == 0 or min(port_counts) > 0, f"unexpected dark port at k={k}")
        law = ((1 - phase[0]) / 2, (1 + phase[0]) / 2)
        need(tuple(Fraction(n, total) for n in port_counts) == law, f"law at k={k}")

        padded_counts = counts_by_port(tuple(a * a for a in apply(H, padded_state)))
        need(sum(padded_counts) == padded_total, f"padded event total at k={k}")
        need(
            tuple(Fraction(n, padded_total) for n in padded_counts) == law,
            f"padded bypass changes port law at k={k}",
        )

        if k <= 2:
            for reverse in (False, True):
                routed = run(initial_cloud, (H,) + (shifter,) * k + (H,), reverse)
                need(
                    routed == rail_counts, f"explicit routing k={k}, reverse={reverse}"
                )
            raw_counts.append(port_counts)

        state = apply(shifter, state)
        padded_state = apply(padded_bypass, padded_state)
        num = gaussian_mul(num, Z_NUM)
        den *= Z_DEN
        total *= Z_DEN
        padded_total *= Z_DEN**2

    need(raw_counts == [(0, 16), (16, 64), (256, 144)], "explicit port counts changed")
    print(
        f"Explicit route counts k=0,1,2 (two matchings): {raw_counts}; port 0 dark at k=0."
    )
    print("Compressed k=0..128: frequencies (1-Re(z^k), 1+Re(z^k))/2; total 16*5^k.")
    print("Gain 5 is minimal in the equal-norm two-Gaussian-multiplier family only.")
    print("Both arms act. Bare identity bypass is unbalanced; gain-25 5I bypass works.")
    print(
        "Fixed non-Clifford angular target (5+12i)/13; target port-1 probability 9/13."
    )
    print("Chord-squared gaps (exact comparisons; outward decimal bounds below):")
    returns = []
    calibrations = []
    readout_calibrations = []
    for last in WINDOWS:
        window = phase_orbit[: last + 1]
        return_gap, return_k = min(
            (chord_squared(point, IDENTITY), k) for k, point in enumerate(window) if k
        )
        target_gap, target_k = min(
            (chord_squared(point, TARGET), k) for k, point in enumerate(window)
        )
        readout_gap, readout_k = min(
            (abs(point[0] - TARGET[0]) / 2, k) for k, point in enumerate(window)
        )
        need(
            min(return_gap, target_gap, readout_gap) > 0, "unexpected exact calibration"
        )
        returns.append(return_k)
        calibrations.append(target_k)
        readout_calibrations.append(readout_k)
        print(
            f"  k≤{last}: return k={return_k} {bracket(return_gap)}; "
            f"target k={target_k} {bracket(target_gap)}; "
            f"nearest port reading k={readout_k} {bracket(readout_gap)}."
        )
    need(returns == [7, 7, 27, 61, 61], "nearest-return holdout drift")
    need(calibrations == [8, 8, 8, 8, 69], "nearest-calibration holdout drift")
    need(readout_calibrations == [8, 8, 8, 8, 69], "nearest port-reading holdout drift")
    print(
        "Density is an unbounded-iteration statement, not exact or finite-resource access."
    )


if __name__ == "__main__":
    main()
