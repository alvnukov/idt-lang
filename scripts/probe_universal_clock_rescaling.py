"""Can an angle change imitate common clock and ruler factors in a supplied walk?

Per tick/site the positive principal band satisfies cos(w)=cos(theta) cos(k).
Compare homogeneous regions by w_phi(k) = N w_theta(B k), N,B > 0; k is in
radians/site and w in radians/tick. A fixed ruler means B=1. "Gap" below is
the positive rest phase (half the eigenphase splitting). The negative branch
is the partner of the same band, not a second independent clock.

Near rest, for 0 < theta < pi/2, w = theta + p*k^2/2 - p*(1+3*p^2)*k^4/24
+ O(k^6), p=cot(theta). Rest and curvature always admit a single-band fit:
N=phi/theta and B^2=cot(phi)/(N*p). But J=-w(0)*w''''(0)/w''(0)^2 is
invariant under both rescalings and equals theta*(tan(theta)+3*cot(theta)).
It is strictly increasing: for t=tan(theta), t^2*J'(theta) equals
F=t^3+3t-(1+t^2)*(3-t^2)*atan(t); F(0)=0 and
dF/dt=4t*(t-atan(t)+t^2*atan(t)) > 0. This is an analytic argument;
the executable checks exact examples, not a machine proof of monotonicity.

For two distinct acute gaps, the candidate common B^2 must equal
r(theta)=cot(N*theta)/(N*cot(theta)) for both. With both new gaps acute and
N != 1, d(log r)/dtheta=2/sin(2*theta)-2*N/sin(2*N*theta) has a strict
sign since sin(x)/x decreases on (0,pi). No common B then fits both.

In the strict cone limit (theta,k)=(epsilon*m,epsilon*q), w/epsilon tends
to sqrt(m^2+q^2). Proportionally changed masses now imitate (N,1/N) even
across multiple species. This compares dispersions only, not inhomogeneous
propagation, a sourced metric, physical clocks, or measured redshift.

Run: python3 -O -m scripts.probe_universal_clock_rescaling
"""

from fractions import Fraction as F
from math import acos, atan2, cos, hypot, isclose, pi, sqrt
from typing import NamedTuple


def check(condition: bool, message: str) -> None:
    if not condition:
        raise ValueError(message)


class RestJet(NamedTuple):
    """Gap in units of the reference angle; derivatives wrt k in lattice units."""

    gap_units: F
    d2: F
    d4: F

    def rescale(self, rate: F, ruler_squared: F) -> "RestJet":
        return RestJet(
            rate * self.gap_units,
            rate * ruler_squared * self.d2,
            rate * ruler_squared * ruler_squared * self.d4,
        )

    def diagnostic(self) -> F:
        """J divided by the reference angle: exact in the doubling fixture."""
        return -self.gap_units * self.d4 / (self.d2 * self.d2)


def rest_jet(gap_units: F, cotangent: F) -> RestJet:
    check(cotangent > 0, "requires a gapped, nonflat acute band")
    d2 = cotangent
    d4 = -cotangent * (1 + 3 * cotangent * cotangent)
    # Independently match the k^2 and k^4 coefficients of cos(w)/cos(theta).
    check(d2 / cotangent == 1, "quadratic cosine coefficient")
    check(-d4 / cotangent - 3 * d2 * d2 == 1, "quartic cosine coefficient")
    return RestJet(gap_units, d2, d4)


def band(angle: float, k: float) -> float:
    return acos(cos(angle) * cos(k))


def check_species(p: F) -> tuple[F, F]:
    """Integer signed coin (p,1) doubled by rotation composition; p > 1."""
    check(p > 1, "doubled gap must stay acute")
    # (p+i)^2=(p^2-1)+2p*i, so phi=2*theta without a numerical angle fit.
    rate = F(2)
    new_p = (p * p - 1) / (2 * p)
    old, changed = rest_jet(F(1), p), rest_jet(rate, new_p)
    b2 = changed.d2 / (rate * old.d2)
    fitted = old.rescale(rate, b2)
    check(fitted[:2] == changed[:2], "rest and curvature should admit one fit")
    check(old.rescale(rate, F(1)).d2 != changed.d2, "fixed ruler should reject")
    check(fitted.d4 != changed.d4, "the quartic lattice response distinguishes it")
    check(fitted.diagnostic() == old.diagnostic(), "rescaling changed J")
    check(changed.diagnostic() > old.diagnostic(), "coin change should raise J")
    check(old.rescale(F(3, 2), F(1)).diagnostic() == old.diagnostic(), "retiming")

    # A separate floating-point check against the branch, not derivative fitting.
    theta, phi = atan2(1.0, float(p)), atan2(1.0, float(new_p))
    check(isclose(phi, 2 * theta, rel_tol=1e-14), "angle doubling")
    for angle in (theta, phi):
        check(isclose(band(angle, pi / 2), pi / 2, abs_tol=1e-14), "fixed-ruler pivot")
    # Even with its fitted ruler, this band's finite-k prediction fails.
    k = 0.5
    predicted = float(rate) * band(theta, sqrt(float(b2)) * k)
    check(
        not isclose(band(phi, k), predicted, rel_tol=1e-12, abs_tol=1e-12),
        "finite-k separation lost in this numeric fixture",
    )
    return b2, changed.diagnostic() / old.diagnostic()


def check_continuum() -> None:
    # Exact squared positive-energy identity for illustrative rational m, q, N.
    for rate in (F(1, 2), F(3, 2), F(2)):
        for m in (F(0), F(1, 2), F(3, 4)):
            for q in (F(-5, 3), F(0), F(2, 7)):
                changed = (rate * m) ** 2 + q**2
                common = rate**2 * (m**2 + (q / rate) ** 2)
                check(changed == common, "strict continuum rescaling ambiguity")
    # Numeric convergence illustration, not a lattice identity or an error bound.
    m_float, q_float = 0.5, 0.75
    continuum = hypot(m_float, q_float)
    errors = [
        abs(band(eps * m_float, eps * q_float) / eps - continuum)
        for eps in (0.5, 0.25, 0.125)
    ]
    check(0 < errors[2] < errors[1] < errors[0], "cone approach on this sample")


def check_endpoints() -> None:
    # Neither the cusped massless nor flat pi/2 band has the acute diagnostic.
    for k in (-1.0, 0.0, 0.5, 1.0):
        check(isclose(band(0.0, k), abs(k), abs_tol=1e-14), "massless cusp")
        check(isclose(2 * band(0.0, k / 2), abs(k), abs_tol=1e-14), "cone fixes NB")
        check(isclose(band(pi / 2, k), pi / 2, abs_tol=1e-14), "flat band")


def main() -> None:
    first, second = check_species(F(2)), check_species(F(3))
    check(first == (F(3, 16), F(43, 39)), "first species expected rational factors")
    check(second[0] == F(2, 9), "second species expected ruler")
    check(first[0] != second[0], "two curves must require different rulers")
    check_continuum()
    check_endpoints()
    print("Finite lattice: a fixed-ruler pi/2 pivot excludes nontrivial clock scaling.")
    print(
        f"One clock, free ruler: N=2, B^2={first[0]} fits gap/curvature; J ratio={first[1]}."
    )
    print(f"Second clock at N=2 needs B^2={second[0]}; no common quadratic fit.")
    print(
        "Exact rational fixtures; direct phase, endpoint and convergence checks use floats."
    )
    print(
        "Strict continuum: m -> N*m and (clock,ruler)=(N,1/N) give identical dispersions."
    )
    print("Massless cone fixes NB only; flat band does not constrain the ruler.")
    print(
        "Supplied bands only: no operational clock, measured redshift, metric or gravity derivation."
    )


if __name__ == "__main__":
    main()
