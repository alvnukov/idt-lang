"""Two harmonics of ONE reused link phase, not two independent draws.

Assume calibrated equal-arm cosine comparison, opposite reference settings,
all emitted trials counted, two forward exposures to precisely the same link,
and the same distribution across the one- and two-exposure settings. A phase
is held fixed within a shot. These hypotheses are not inferred from counts.

The supplied signed two-arm recipe diag(2-i,2+i) in probe_integer_phase_orbit
has relative phase (2+i)/(2-i)=(3+4i)/5. This is not itself a single
lossless oriented integer-rail change (the latter class only admits C4).
Real-part readout cannot distinguish the fixed rotation from an equal mixture
of it and its conjugate if the draw is reused. Neither is physical link noise
data. Here C_N means roots of unity referred to the fixed calibrated zero,
not adjustable phase offsets, arbitrary response tables, or a bound on the
number of hidden labels: the conjugate example itself needs only two labels.
Unlike probe_cyclic_shutter_holdout this repeats the link in series;
it does not copy/open distinct alternatives before a readout.

Run: python3 -O -m scripts.probe_link_phase_harmonics
"""

from fractions import Fraction as F
from math import atan2, cos, pi

Phase = tuple[F, F]
Law = tuple[tuple[Phase, F], ...]
C4 = ((F(1), F(0)), (F(0), F(1)), (F(-1), F(0)), (F(0), F(-1)))


def check(ok: bool, why: str) -> None:
    if not ok:
        raise ValueError(why)


def mul(z: Phase, w: Phase) -> Phase:
    a, b = z
    c, d = w
    return a * c - b * d, a * d + b * c


def moments(law: Law) -> tuple[F, F, F]:
    check(
        all(w >= 0 and a * a + b * b == 1 for (a, b), w in law)
        and sum(w for _, w in law) == 1,
        "positive normalized phase law",
    )
    m1 = sum((w * z[0] for z, w in law), F(0))
    shared = sum((w * mul(z, z)[0] for z, w in law), F(0))
    independent = sum((w * v * mul(z, y)[0] for z, w in law for y, v in law), F(0))
    variance = sum((w * (z[0] - m1) ** 2 for z, w in law), F(0))
    check(shared - (2 * m1 * m1 - 1) == 2 * variance, "variance boundary")
    for m in (m1, shared, independent):
        plus, minus = (1 + m) / 2, (1 - m) / 2
        check(
            plus >= 0 and minus >= 0 and plus + minus == 1 and plus - minus == m,
            "calibrated all-emission contrasts",
        )
    return m1, shared, independent


def c4_witness(m1: F, m2: F) -> Law | None:
    """The two transverse site weights can be split arbitrarily. Split evenly."""
    longitudinal = ((1 + m2 + 2 * m1) / 4, (1 + m2 - 2 * m1) / 4)
    transverse = (1 - m2) / 4
    weights = longitudinal[0], transverse, longitudinal[1], transverse
    if min(weights) < 0:
        return None
    law = tuple(zip(C4, weights, strict=True))
    check(moments(law)[:2] == (m1, m2), "C4 inverse weights")
    return law


def exact_cycle_obstruction() -> None:
    # If z^n=1 then S_n(z+z^-1)=2, where S_0=2, S_1=x, S_n=x S_{n-1}-S_{n-2}.
    # A_n=5^n S_n(6/5) => A_n=6A_{n-1}-25A_{n-2}; A_n=1 mod 5 for EVERY
    # n>=1 by induction. It can never equal 2*5^n. The loop checks samples.
    older, current = 2, 6
    for n in range(1, 65):
        check(current % 5 == 1 and current != 2 * 5**n, "root-of-unity residue")
        older, current = current, 6 * current - 25 * older


def main() -> None:
    z: Phase = (F(3, 5), F(4, 5))
    zbar: Phase = (z[0], -z[1])
    check(mul(z, (F(2), F(-1))) == (F(2), F(1)), "supplied relative-phase recipe")
    law: Law = ((z, F(1, 2)), (zbar, F(1, 2)))
    m1, m2, iid = moments(law)
    check((m1, m2, iid) == (F(3, 5), F(-7, 25), F(9, 25)), "reused vs redrawn phase")
    check(moments(((z, F(1)),))[:2] == (m1, m2), "cosines do not identify sign noise")
    check(
        c4_witness(m1, m2) is None and c4_witness(m1, iid) is not None,
        "C4 hinge and redraw control",
    )
    gap = 2 * abs(m1) - 1 - m2
    check(
        gap == F(12, 25) and m2 == 2 * m1 * m1 - 1,
        "four-site gap and exact variance saturation",
    )
    # For coordinate errors e1,e2 the hinge can decrease by at most 2e1+e2.
    # The equal-width threshold is sharp, since the touching point has a law.
    radius = gap / 3
    check(
        radius == F(4, 25) and c4_witness(m1 - radius, m2 + radius) is not None,
        "sharp rectangle boundary",
    )
    check(c4_witness(m1 - F(3, 20), m2 + F(3, 20)) is None, "strict robust exclusion")
    exact_cycle_obstruction()

    # Exact larger-cycle control: conjugate sixth roots have cos=1/2 and
    # cos(2phi)=-1/2. Weights (1/5,2/5,0,0,0,2/5) pin the first moment.
    sixth = ((F(1), F(1, 5)), (F(1, 2), F(4, 5)))
    c6m1 = sum((w * c for c, w in sixth), F(0))
    c6m2 = sum((w * (2 * c * c - 1) for c, w in sixth), F(0))
    check(
        c6m1 == m1 and c6m2 == F(-1, 5) and c4_witness(c6m1, c6m2) is None,
        "C6 can violate C4",
    )
    # Nearest N-cycle angle differs by <=pi/N. The two cosine errors are
    # at most pi/N and 2pi/N, respectively, for every N (derivative bounds).
    # Irrational trig below only illustrates the uniform analytic estimate.
    angle = atan2(4, 3)
    for n in (16, 128, 4096):
        k = round(n * angle / (2 * pi))
        theta = 2 * pi * k / n
        check(
            abs(cos(theta) - float(m1)) <= 4 / n
            and abs(cos(2 * theta) - float(m2)) <= 8 / n,
            "numeric finite-cycle approximation",
        )
    print(
        "Reused phase: (m1,m2)=(3/5,-7/25); C4 misses by 12/25. Equal contrast errors <4/25 still exclude C4."
    )
    print(
        "Independent conjugate draws: m2=9/25, compatible with C4. A fixed sign gives the same reused cosines."
    )
    print(
        "Exact variance saturation rules out root-of-unity phases here, not finite hidden labels. C6 already violates C4, and large cycles approximate both moments arbitrarily well."
    )
    print(
        "Calibrated comparison, shared link and positive phase-stock model are supplied; no physical link, field or noise law is derived."
    )


if __name__ == "__main__":
    main()
