"""Does a pair of isotropic Weyl-like deviations already behave as a photon?

Test the leading Weyl Hamiltonian in the supplied common momentum chart,
with c=1 for the algebra. A spin-one symbol and a massless two-body quantum
particle with transverse polarizations, Bose statistics and local single
absorption are distinct contracts. No latter property is imposed to pass.
This is not an assertion about all composite photons or the exact full
collision walk at finite wavelength.
"""

from __future__ import annotations

from fractions import Fraction as F
from itertools import product
from math import isqrt

from scripts import probe_balanced_phase_composition as b
from scripts.gaussian_dyadic_words import g

I2 = b.identity(2)
X = b.matrix(((0, 1), (1, 0)))
Z = b.matrix(((1, 0), (0, -1)))
UPUP = (1, 0, 0, 0)
DOWNDOWN = (0, 0, 0, 1)
LONG = (0, 1, 1, 0)
SINGLET = (0, 1, -1, 0)


def need(ok: bool, reason: str) -> None:
    if not ok:
        raise ArithmeticError(reason)


def act(a: b.Matrix, v: tuple[int, ...]) -> tuple[F, ...]:
    return tuple(sum((x * y for x, y in zip(r, v, strict=True)), F(0)) for r in a)


def spin_controls() -> None:
    # K=2 e_z; p1=p2=e_z. Sym² of two Weyl spinors has eigenvalues +2,0,-2.
    h = b.add(b.tensor(Z, I2), b.tensor(I2, Z))
    for v, e in ((UPUP, 2), (LONG, 0), (DOWNDOWN, -2), (SINGLET, 0)):
        need(act(h, v) == tuple(F(e * x) for x in v), "aligned mode generator")
    trans = b.add(b.tensor(X, I2), b.scale(-1, b.tensor(I2, X)))
    need(
        act(trans, UPUP) == tuple(F(-x) for x in SINGLET),
        "relative transverse momentum did not couple singlet",
    )
    need(act(trans, DOWNDOWN) == tuple(F(x) for x in SINGLET), "wrong helicity sign")
    # Positive-energy identical fermions at this identical spatial momentum
    # have a single positive-energy one-body mode, whose exterior square is 0.
    swap = b.matrix(((1, 0, 0, 0), (0, 0, 1, 0), (0, 1, 0, 0), (0, 0, 0, 1)))
    fermion = b.scale(F(1, 2), b.add(b.identity(4), b.scale(-1, swap)))
    need(
        b.trace(fermion) == 1
        and act(fermion, UPUP) == (F(0),) * 4
        and act(fermion, SINGLET) == tuple(F(x) for x in SINGLET),
        "Pauli control",
    )
    # The Bloch vector of one spinor at fixed momentum has momentum zero
    # as a physical bilinear; it transforms differently from a two-body wave.
    phase = g(F(3, 5), F(4, 5))
    need(
        phase * phase.star() == g(1) and phase * phase != g(1),
        "total momentum vs difference",
    )


def pair_energy_grid() -> tuple[int, int]:
    # Compare E=|p|+|q| with |p+q| on all integer vectors of length <=5.
    # Avoid irrational approximations: equality iff p.q>=0 and Cauchy is
    # saturated. Also square the transverse bound only with its sign checked.
    points = tuple(
        v for v in product(range(-5, 6), repeat=3) if 0 < sum(x * x for x in v) <= 25
    )
    hit = miss = 0
    for p in points:
        a = sum(x * x for x in p)
        for q in points:
            c = sum(x * x for x in q)
            dot = sum(x * y for x, y in zip(p, q, strict=True))
            area2 = a * c - dot * dot
            k2 = a + c + 2 * dot
            need(area2 >= 0, "Cauchy")
            if not k2:
                continue
            eq = area2 == 0 and dot > 0
            if eq:
                hit += 1
            else:
                miss += 1
            # 4|r_perp|²=4|p×q|²/|K|². The inequality
            # 2(sqrt(a c)-dot)>=4*area²/k² is equivalent to
            # sqrt(a c)*k² >= dot*k²+2*area² (RHS may be negative).
            rhs = dot * k2 + 2 * area2
            need(rhs <= 0 or a * c * k2**2 >= rhs**2, "transverse mass bound")
    need(hit > 0 and miss > hit, "grid lacked a discriminator")
    # p=(3,0,4), q=(-3,0,4): relative transverse norm 3; equality at 36.
    need((2 * isqrt(25)) ** 2 - 8**2 == 4 * 3**2, "sharp noncollinear bound")
    return hit, miss


def main() -> None:
    spin_controls()
    ok, off = pair_energy_grid()
    print(
        f"Positive-branch free Weyl-pair continuum: {ok} lightlike and {off} timelike composite momenta on the finite ordered grid (K nonzero). For relative transverse r, (E/c)^2-|K|² >= 4|r_perp|²."
    )
    print(
        "At fixed nonzero total momentum the massless set has zero 3D relative-momentum measure; no nonzero square-integrable free relative packet lies entirely on it. Binding, confinement to a line, or a separate mode changes the problem."
    )
    print(
        "At equal momenta the spin-one triplet has signs +,0,-, not two independent positive-frequency helicities; transverse relative momentum mixes a triplet into the singlet. Identical fermions cannot both occupy the aligned positive mode."
    )
    print(
        "This conditional near-cone test neither constructs nor excludes a general photon. Bose counting, detector absorption and common light speed for other carriers remain separate."
    )


if __name__ == "__main__":
    main()
