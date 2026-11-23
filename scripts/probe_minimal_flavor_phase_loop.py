"""Can a shared direction and two sector-specific directions permit flavor CP?

SUPPLY complex three-family space, a common charged-current identification,
two Hermitian mass-squared proxies, and the interpretation of their relative
eigenbases. Put P_v=vv* (unnormalized), H_u=aI+bP_s+cP_u, H_d=eI+fP_s+gP_d
with real coefficients. The six constants, rank-one coupling rule, and the
assignment of branch directions to quark sectors are NOT derived from clocks.
The illustrative proxies are positive semidefinite; signed coefficients in
algebraic controls need not represent squared masses.

With V=[s,u,d], G=V*V, write both non-scalar parts as V D_j V*. The middle
matrix of the commutator is M_ij=(D_ui D_dj-D_di D_uj)G_ij. Its diagonal
vanishes and M is anti-Hermitian. Only the two oriented 3-cycles contribute
to det(M). Consequently det([H_u,H_d])=2i det(G) b f c^2 g^2 Im(G12 G23 G31).
This is an algebraic identity, including singular V, not a Lean proof.
The three-ray product is invariant under individual ray rephasings. A
nonreal product is necessary but NOT sufficient: the three rays must span.
Two shared rays leave a common dark line. One rank-one perturbation alone
leaves a repeated eigenvalue in that sector. Minimality ONLY concerns this
rank-one deformation ansatz, not all models of three-family mixing.

For distinct squared masses the magnitude of the dimensionful commutator
determinant equals 2 |J| times both absolute Vandermondes. This follows
by diagonalizing one proxy and expanding the two oriented 3-cycles. The
dimensionless J additionally uses the usual common weak-basis/unitary
mixing interpretation; changing the units of either H changes det(C).
See Jarlskog, https://doi.org/10.1103/PhysRevLett.55.1039 .

This is distinct from probe_ckm_raw_family_wall (both mass eigenbases
are raw words there; here the eigenbases diagonalize supplied mass
proxies) and probe_packet_triad_phase (a bosonic optical observable).
For a fixed external comparator, LHCb, JHEP 02 (2021) 169, original
https://arxiv.org/abs/2010.08483, https://doi.org/10.1007/JHEP02(2021)169:
9 fb^-1, charged B -> DK and D pi, binned D -> K_S h+h- data interpreted
as gamma=68.7(+5.2,-5.1) degrees. Independent of modeling the D decay
amplitude does not mean independent of the weak-decay interpretation.
Neither gamma nor data were used to choose the illustrative directions;
gamma is not J, a Gram phase, or this dimensionful determinant. On the
specific sorted k=1 toy the actual gamma quartet gives atan(2); |V_ud|^2
is already grossly incompatible with the raw-family probe's fixed PDG
2024 comparator. The equal spectra across sectors are also unrealistic.
No fit, parameter selection, joint data test or confidence statement.
"""

import sys
from fractions import Fraction as F
from itertools import permutations
from math import atan2, degrees
from pathlib import Path

if not __package__:
    sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
from scripts.gaussian_dyadic_words import ONE, ZERO, I, eye, g, run
from scripts.probe_ckm_raw_family_wall import PDG, adjoint, determinant, multiply


def need(ok, message):
    if not ok:
        raise ArithmeticError(message)


def linear(*terms):
    return tuple(
        tuple(sum((g(k) * m[i][j] for k, m in terms), ZERO) for j in range(3))
        for i in range(3)
    )


def projector(v):
    return tuple(tuple(a * b.star() for b in v) for a in v)


def scale_vec(z, v):
    return tuple(z * a for a in v)


def comm(x, y):
    return linear((1, multiply(x, y)), (-1, multiply(y, x)))


def charpoly(x):
    tr = sum((x[i][i] for i in range(3)), ZERO)
    pairs = sum(
        (
            x[i][i] * x[j][j] - x[i][j] * x[j][i]
            for i in range(3)
            for j in range(i + 1, 3)
        ),
        ZERO,
    )
    coeffs = (ONE, ZERO - tr, pairs, ZERO - determinant(x))
    need(all(q.im == 0 for q in coeffs), "nonreal spectrum coefficients")
    return tuple(q.re for q in coeffs)


def discriminant(p):
    _, a, b, c = p
    return a * a * b * b - 4 * b**3 - 4 * a**3 * c - 27 * c * c + 18 * a * b * c


def proxies(s, u, d, coeffs):
    a, b, c, e, f, h = coeffs
    return (
        linear((a, eye(3)), (b, projector(s)), (c, projector(u))),
        linear((e, eye(3)), (f, projector(s)), (h, projector(d))),
    )


def read(s, u, d, coeffs=(0, 1, 1, 0, 1, 1)):
    _, b, c, _, f, h = coeffs
    v = tuple(zip(s, u, d, strict=True))
    gram = multiply(adjoint(v), v)
    volume = determinant(gram)
    loop = gram[0][1] * gram[1][2] * gram[2][0]
    x, y = proxies(s, u, d, coeffs)
    cp = determinant(comm(x, y))
    need(
        volume == g(determinant(v).norm2())
        and cp == g(0, 2 * volume.re * b * f * c * c * h * h * loop.im),
        "Gram factorization vs direct determinant",
    )
    polys = (charpoly(x), charpoly(y))
    du, dd = map(discriminant, polys)
    need(
        du >= 0 and dd >= 0 and (du * dd > 0 or cp == ZERO),
        "spectral degeneracy control",
    )
    j2 = cp.norm2() / (4 * du * dd) if du * dd else None
    return cp.im, volume.re, loop, polys, j2


def swap_basis(v, p):
    return tuple(v[i] for i in p)


def relabel_matrix(x, p):
    return tuple(tuple(x[i][j] for j in p) for i in p)


def illustrative():
    s = (ONE, ONE, ONE)
    u = (ONE, ONE, ZERO)
    d = (ONE, I, ONE)
    d0 = (ONE, ONE, I)
    hit = read(s, u, d)
    dark = read(s, u, d0)
    need(
        hit[:3] == (8, 2, g(6, 2)) and dark[:3] == (0, 0, g(8, -4)),
        "phase alone is not enough",
    )
    need(
        hit[3] == dark[3] == ((1, -5, 2, 0), (1, -6, 4, 0))
        and hit[4] == F(1, 1360)
        and dark[4] == 0,
        "individual simple positive-semidefinite spectra",
    )
    h, h0 = (
        proxies(s, u, d, (0, 1, 1, 0, 1, 1))[1],
        proxies(s, u, d0, (0, 1, 1, 0, 1, 1))[1],
    )
    need(
        tuple(h[i][i] for i in range(3)) == tuple(h0[i][i] for i in range(3)),
        "marginal diagonal",
    )
    need(
        read(scale_vec(I, s), scale_vec(g(-1), u), scale_vec(g(0, -1), d)) == hit,
        "individual ray phases",
    )
    for p in permutations(range(3)):
        need(
            read(*(swap_basis(v, p) for v in (s, u, d))) == hit,
            "simultaneous family relabeling",
        )
    need(read(s, u, tuple(z.star() for z in d))[0] == -8, "conjugate theory")
    for coeffs in (
        (3, 2, 3, 7, 5, 2),
        (-2, 1, -1, 3, -1, -2),
        (0, 1, 0, 0, 1, 1),
        (9, 0, 1, 7, 1, 1),
    ):
        read(s, u, d, coeffs)
    need(
        read(s, u, d, (3, 1, 0, 7, 1, 1))[4] is None,
        "rank-one sector has repeated eigenvalue",
    )
    return hit, dark


def native_clock_controls():
    s, u = (ONE, ONE, ONE), (ONE, ZERO, ZERO)
    polys = ((1, -4, 2, 0), (1, -4, 2, 0))
    results = []
    for k in range(4):
        raw = run(eye(3), (("T", 0, 1),) * k)
        d = tuple(row[0] for row in raw)
        res = read(s, u, d)
        need(res[3] == polys, "individual spectra drifted over the native word orbit")
        results.append(res)
    need(
        [r[0] for r in results] == [0, F(1, 2), 0, F(-1, 2)]
        and [r[1] for r in results] == [0, F(1, 2), 1, F(1, 2)]
        and [r[4] for r in results] == [0, F(1, 128**2), 0, F(1, 128**2)],
        "native four-turn fiber; same spectra, phase sign, two distinct zeros",
    )
    # A regular commuting clock is not itself a family symmetry-breaking
    # field. The commutant of a 3-cycle is circulant: entry (i,j) depends
    # only on j-i mod 3. Circulants are polynomials in that same cycle.
    # Complex circulants need not have spectral degeneracy (example below).
    cyc = ((0, 1, 2), (1, 2, 0), (2, 0, 1))

    def twirl(x):
        return linear(*((F(1, 3), relabel_matrix(x, p)) for p in cyc))

    d = tuple(row[0] for row in run(eye(3), (("T", 0, 1),)))
    x, y = proxies(s, u, d, (0, 1, 1, 0, 1, 1))
    zero = linear((0, eye(3)))
    anticirc = ((ZERO, I, g(0, -1)), (g(0, -1), ZERO, I), (I, g(0, -1), ZERO))
    need(
        twirl(anticirc) == anticirc and discriminant(charpoly(anticirc)) > 0,
        "complex simple clock control",
    )
    need(
        comm(twirl(x), twirl(y)) == zero and comm(anticirc, twirl(x)) == zero,
        "clock-commuting sectors",
    )
    # Do not average each tensor before computing an invariant of a jointly
    # relabeled pair. Without a physical averaging/decoherence rule these
    # are different experiments; an anonymous correlated pair can carry CP.
    need(
        all(
            determinant(comm(relabel_matrix(x, p), relabel_matrix(y, p)))
            == g(0, F(1, 2))
            for p in cyc
        ),
        "spurious loss under a shared coordinate change",
    )
    return results


def sorted_angle_control(expected_j2):
    # Sort each proxy by its nondegenerate eigenvalues 0,2-sqrt(2),2+sqrt(2).
    # Since H_d=T H_u T*, its eigenvectors may be chosen T times the real
    # up eigenvectors. T=I+(i-1)ww*, w=(1,-1,0)/sqrt(2). In that real
    # eigenbasis write r_j=|w_j|^2. Only weights, no eigensolver, needed.
    s, u = (ONE, ONE, ONE), (ONE, ZERO, ZERO)
    t = I - ONE
    raw = run(eye(3), (("T", 0, 1),))
    w0 = (ONE, g(-1), ZERO)
    wproj = linear((F(1, 2), projector(w0)))
    ident = eye(3)
    need(
        raw
        == tuple(
            tuple(ident[i][j] + t * wproj[i][j] for j in range(3)) for i in range(3)
        ),
        "addressed difference eigenvector",
    )
    d = tuple(row[0] for row in raw)
    x, y = proxies(s, u, d, (0, 1, 1, 0, 1, 1))
    need(
        multiply(multiply(raw, x), adjoint(raw)) == y,
        "down eigenbasis not the shared raw-image basis",
    )
    light = (ZERO, ONE, g(-1))
    need(
        all(
            sum((x[i][j] * light[j] for j in range(3)), ZERO) == ZERO for i in range(3)
        ),
        "lightest family direction",
    )
    r0 = sum((a.star() * b for a, b in zip(light, w0, strict=True)), ZERO).norm2() / 4
    moment = sum(
        (w0[i].star() * x[i][j] * w0[j] for i in range(3) for j in range(3)), ZERO
    ) * g(F(1, 2))
    need(
        r0 == F(1, 4) and moment == g(F(1, 2)) and charpoly(x) == (1, -4, 2, 0),
        "spectral weights",
    )
    # r1+r2=1-r0. Their first moment implies
    # sqrt(2)*(r2-r1)=moment-2*(1-r0). Hence r1*r2 follows rationally.
    r12 = ((1 - r0) ** 2 - (moment.re - 2 * (1 - r0)) ** 2 / 2) / 4
    diag = ONE + t * g(r0)
    # -V_ud V_cd* V_cb V_ub*: denominator scaling of gamma is positive.
    quartet = (ZERO - diag) * t.star() * t * t.star() * g(r0 * r12)
    need(
        r12 == F(1, 64)
        and quartet == g(F(1, 256), F(1, 128))
        and quartet.im**2 == expected_j2,
        "sorted gamma quartet vs independent commutator",
    )
    mag2 = diag.norm2()
    need(
        mag2 == F(5, 8) and mag2 < PDG[0][0].low ** 2,
        "isolated angular proximity cannot repair the |Vud| comparator",
    )
    return degrees(atan2(quartet.im, quartet.re)), mag2


def main():
    h, d = illustrative()
    rows = native_clock_controls()
    angle, mag2 = sorted_angle_control(rows[1][4])
    print(
        "Same spectral polynomials (up, down):",
        tuple(tuple(int(z) for z in poly) for poly in h[3]),
        "; det(C)/i:",
        h[0],
        d[0],
        "; Im(loop):",
        h[2].im,
        d[2].im,
        "; Gram determinants:",
        h[1],
        d[1],
    )
    print(
        "Native T01^k on the sector-specific seed, k=0..3; det(C)/i:",
        tuple(str(r[0]) for r in rows),
    )
    print(
        "Absolute J under the supplied mixing interpretation: 0, 1/128, 0, 1/128. No masses or CKM fit."
    )
    print(
        "Individually clock-invariant sectors commute; jointly relabeling the same oriented pair preserves its invariant."
    )
    print(
        f"Specific k=1 sorted toy: gamma=atan(2)={angle:.3f} degrees; |Vud|^2={mag2}, outside the frozen PDG 2024 fitted range."
    )
    print(
        "External decay-angle comparator only: LHCb gamma = 68.7 (+5.2,-5.1) degrees; not a measurement of these proxies or J."
    )


if __name__ == "__main__":
    main()
