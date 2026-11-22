"""What a two-state linearization does (and does not) fix about a cone.

In a supplied momentum frame q, suppose a crossing has a Hermitian linear
part H(q) = (t.q) I + sum_j q_j A_j with A_j traceless. Write A_j = b_j.sigma
and B = [b_1 ... b_d]. The shifted energies obey

    (E - t.q)^2 = q^T G q,   G_jk = Tr(A_j A_k)/2 = (B^T B)_jk.

G is positive semidefinite, rank(G)=rank(B)<=min(d,3). Real-symmetric A_j
have no sigma_y component, hence rank <= 2. This permits fewer dimensions,
degenerate directions, and tilt; neither space dimension nor an untilted
full-rank cone follows just from having two internal states.

The lattice control uses position on a common integer lattice and one
tick for all components. Each directional unitary has Laurent exponents
-3,-1,1,3; composing one factor per axis permits at most 3 sites along
each axis per tick. This common causal upper bound does not identify
the cone metrics: without flavor mixing the speeds are 3 and 1
(G=9I and G=I), in the same space/time frame. A constant spin-basis rotation,
by contrast, preserves G by trace invariance.

In the mixed walk the speed operators on the flavor space are
V_z=diag(3,1) for x,z and V_x=[[2,1],[1,2]] for y. Each factor still has the
same support bound and is unitary by orthogonal spectral projectors.
These speed operators do not commute; no fixed rank-one flavor projector
commutes with every directional factor. The axial slopes are still
-3,-1,1,3. Along q=(1,1,0) the mixed slopes are -4,-2,2,4:
mixing changes the dispersion, not just the names of the two sectors.
This is a coherent linear mixing countercontrol, not a many-body model
or a claim about the long-distance flow of interacting theories.

For a full Pauli triplet a putative 2x2 Hermitian anticommuting mass
M=m0 I + m.sigma must obey {M,sigma_j}=2m0 sigma_j+2m_j I=0 for all j;
then M=0. A rank-two restriction admits a mass on the unused axis.
In four components, Gamma_j=tau_z tensor sigma_j admit beta=tau_x tensor I,
so (sum_j q_j Gamma_j + m beta)^2 = (|q|^2+m^2) I. These are checks on
supplied generators, not a physical derivation or a claim that a specific
symmetry or mechanism cannot enforce a common cone.
"""

from __future__ import annotations

from collections.abc import Sequence
from dataclasses import dataclass
from fractions import Fraction as F
from itertools import product

Vector = tuple[F, F, F]
Phase = tuple[F, F]
RationalMatrix = tuple[tuple[F, ...], ...]


@dataclass(frozen=True)
class C:
    """A Gaussian rational; no floating-point comparisons in the fixture."""

    re: F
    im: F = F(0)

    def __add__(self, other: C) -> C:
        return C(self.re + other.re, self.im + other.im)

    def __mul__(self, other: C) -> C:
        return C(
            self.re * other.re - self.im * other.im,
            self.re * other.im + self.im * other.re,
        )

    def conj(self) -> C:
        return C(self.re, -self.im)


Matrix = tuple[tuple[C, ...], ...]
ZERO, ONE, MINUS = C(F(0)), C(F(1)), C(F(-1))
VECTORS: tuple[Vector, Vector, Vector] = (
    (F(1), F(0), F(0)),
    (F(0), F(1), F(0)),
    (F(0), F(0), F(1)),
)


def check(condition: bool, message: str) -> None:
    """Keep checks active under python -O."""
    if not condition:
        raise AssertionError(message)


def identity(n: int) -> Matrix:
    return tuple(tuple(ONE if i == j else ZERO for j in range(n)) for i in range(n))


def mul(a: Matrix, b: Matrix) -> Matrix:
    return tuple(
        tuple(
            sum((x * y for x, y in zip(row, col, strict=True)), ZERO) for col in zip(*b)
        )
        for row in a
    )


def add(a: Matrix, b: Matrix) -> Matrix:
    return tuple(
        tuple(x + y for x, y in zip(ar, br, strict=True))
        for ar, br in zip(a, b, strict=True)
    )


def scale(s: C, a: Matrix) -> Matrix:
    return tuple(tuple(s * x for x in row) for row in a)


def dagger(a: Matrix) -> Matrix:
    return tuple(tuple(x.conj() for x in col) for col in zip(*a))


def trace(a: Matrix) -> C:
    return sum((row[i] for i, row in enumerate(a)), ZERO)


def kron(a: Matrix, b: Matrix) -> Matrix:
    return tuple(tuple(x * y for x in ar for y in br) for ar in a for br in b)


def det2(a: Matrix) -> C:
    return a[0][0] * a[1][1] + MINUS * a[0][1] * a[1][0]


def pauli(v: Vector) -> Matrix:
    x, y, z = v
    return (C(z), C(x, -y)), (C(x, y), C(-z))


SIGMA = tuple(pauli(v) for v in VECTORS)
I2, I4 = identity(2), identity(4)


def linear_combination(a: Sequence[Matrix], q: Sequence[F]) -> Matrix:
    result = scale(ZERO, a[0])
    for arg, mat in zip(q, a, strict=True):
        result = add(result, scale(C(arg), mat))
    return result


def dot(a: Sequence[F], b: Sequence[F]) -> F:
    return sum((x * y for x, y in zip(a, b, strict=True)), F(0))


def gram(columns: Sequence[Vector]) -> RationalMatrix:
    return tuple(tuple(dot(u, v) for v in columns) for u in columns)


def trace_gram(matrices: Sequence[Matrix]) -> RationalMatrix:
    def inner(a: Matrix, b: Matrix) -> F:
        t = trace(mul(a, b))
        check(t.im == 0, "real trace inner product")
        return t.re / 2

    return tuple(tuple(inner(a, b) for b in matrices) for a in matrices)


def rank(a: RationalMatrix) -> int:
    rows = [list(row) for row in a]
    pivots = 0
    for j in range(len(a[0])):
        pivot = next((i for i in range(pivots, len(rows)) if rows[i][j]), None)
        if pivot is None:
            continue
        rows[pivots], rows[pivot] = rows[pivot], rows[pivots]
        ref = rows[pivots]
        for i in range(pivots + 1, len(rows)):
            s = rows[i][j] / ref[j]
            rows[i] = [x - s * y for x, y in zip(rows[i], ref, strict=True)]
        pivots += 1
    return pivots


def check_trace_gram() -> int:
    cases = (
        # (derivative columns in supplied directions, tested Gram rank)
        (((1, 2, 3),), 1),
        (((1, 0, 1), (0, 2, 1)), 2),
        (((1, 0, 0), (0, 2, 0), (0, 0, 3)), 3),
        (((1, 0, 1), (0, 0, 2), (1, 0, -1)), 2),  # real symmetric
        (((1, 0, 0), (0, 2, 0), (0, 0, 3), (1, 2, 3)), 3),
    )
    tested = 0
    for values, expected_rank in cases:
        columns = tuple((F(x), F(y), F(z)) for x, y, z in values)
        matrices = tuple(pauli(v) for v in columns)
        g = gram(columns)
        check(trace_gram(matrices) == g and rank(g) == expected_rank, "Gram/rank")
        for mom in product((F(-1), F(0), F(2, 3)), repeat=len(values)):
            traceless = linear_combination(matrices, mom)
            tilt = mom[0] * F(5, 4)
            h = add(traceless, scale(C(tilt), I2))
            qgq = dot(mom, tuple(dot(row, mom) for row in g))
            check(qgq >= 0 and trace(h) == C(2 * tilt), "PSD and tilt trace")
            for e in (F(-2, 3), F(0), F(5, 2)):
                check(
                    det2(add(h, scale(C(-e), I2))) == C((e - tilt) ** 2 - qgq),
                    "independent two-by-two determinant",
                )
                tested += 1
    # An allowed nonzero tilt can put both branches on one side along +x.
    tilted_x = add(SIGMA[0], scale(C(F(5, 4)), I2))
    for root in (F(1, 4), F(9, 4)):
        check(det2(add(tilted_x, scale(C(-root), I2))) == ZERO, "overtilt root")
    return tested


def check_basis_rotation() -> None:
    axes = tuple(scale(C(F(i)), p) for i, p in enumerate(SIGMA, 1))
    w = ((ONE, ZERO), (ZERO, C(F(0), F(1))))
    check(mul(w, dagger(w)) == I2, "unitary basis operation")
    rotated = tuple(mul(mul(w, p), dagger(w)) for p in axes)
    check(
        rotated != axes and trace_gram(rotated) == trace_gram(axes), "basis invariant"
    )


def check_mass() -> None:
    sx, sy, sz = SIGMA
    basis = (I2, sx, sy, sz)
    half = C(F(1, 2))
    zero2, zero4 = scale(ZERO, I2), scale(ZERO, I4)
    for i, p in enumerate(basis):
        for j, axis in enumerate(SIGMA, 1):
            expected = axis if i == 0 else I2 if i == j else zero2
            check(
                scale(half, add(mul(p, axis), mul(axis, p))) == expected,
                "coefficients of the anticommutant map",
            )
    check(mul(sz, sz) == I2, "unused axis is a nonzero square-one mass")
    check(
        all(add(mul(sz, a), mul(a, sz)) == zero2 for a in (sx, sy)),
        "rank-two mass control",
    )

    beta = kron(sx, I2)
    gamma = tuple(kron(sz, a) for a in SIGMA)
    check(mul(beta, beta) == I4, "four-component mass square")
    check(
        all(add(mul(beta, g), mul(g, beta)) == zero4 for g in gamma),
        "four-component anticommuting mass",
    )
    for q in product((F(0), F(1), F(-2)), repeat=3):
        m = F(7, 5)
        h = add(linear_combination(gamma, q), scale(C(m), beta))
        check(mul(h, h) == scale(C(dot(q, q) + m * m), I4), "mass dispersion")


def proj(axis: Matrix, sign: int) -> Matrix:
    return scale(C(F(1, 2)), add(I2, scale(C(F(sign)), axis)))


def axis_terms(spin: Matrix, flavor: Matrix) -> dict[int, Matrix]:
    """Exact coefficients of exp(-i k * step), grouped by integer step."""
    return {
        sign * v: kron(proj(flavor, branch), proj(spin, sign))
        for (v, branch), sign in product(((3, 1), (1, -1)), (-1, 1))
    }


def check_axis_terms(terms: dict[int, Matrix]) -> None:
    zero = scale(ZERO, I4)
    check(set(terms) == {-3, -1, 1, 3}, "shared finite radius per axis")
    check(
        linear_combination(tuple(terms.values()), (F(1),) * len(terms)) == I4,
        "complete step projectors",
    )
    for (i, p), (j, q) in product(terms.items(), repeat=2):
        check(p != zero and mul(p, q) == (p if i == j else zero), "step projectors")


def phase_power(phase: Phase, step: int) -> C:
    c, s = phase
    base = C(c, -s if step > 0 else s)
    value = ONE
    for _ in range(abs(step)):
        value = value * base
    return value


def evolve_axis(terms: dict[int, Matrix], phase: Phase) -> Matrix:
    result = scale(ZERO, I4)
    for n, a in terms.items():
        result = add(result, scale(phase_power(phase, n), a))
    return result


def principal(terms: dict[int, Matrix]) -> Matrix:
    # U_axis(k)=sum_n P_n exp(-i*k*n); derivative at zero is -i times this.
    return linear_combination(tuple(terms.values()), tuple(map(F, terms)))


def flavor_off_diagonal(a: Matrix) -> bool:
    return any(a[i][j] != ZERO for i in range(2) for j in range(2, 4))


def flavor_block(a: Matrix, flavor: int) -> Matrix:
    slots = range(2 * flavor, 2 * flavor + 2)
    return tuple(tuple(a[i][j] for j in slots) for i in slots)


def check_lattice_walks() -> int:
    sx, _, sz = SIGMA
    speeds_z = ((C(F(3)), ZERO), (ZERO, ONE))
    speeds_x = ((C(F(2)), ONE), (ONE, C(F(2))))
    check(mul(speeds_x, speeds_z) != mul(speeds_z, speeds_x), "no common flavor line")

    a = gram(VECTORS)
    b = gram(tuple((3 * x, 3 * y, 3 * z) for x, y, z in VECTORS))
    check(b != a and b == tuple(tuple(9 * x for x in row) for row in a), "unequal G")

    zero4 = scale(ZERO, I4)
    phases: tuple[Phase, ...] = ((F(3, 5), F(4, 5)), (F(5, 13), F(-12, 13)))
    tested = 0
    for mixed in (False, True):
        flavors = (sz, sx if mixed else sz, sz)
        axes = tuple(axis_terms(p, t) for p, t in zip(SIGMA, flavors, strict=True))
        derivatives = tuple(principal(terms) for terms in axes)
        velocities = (speeds_z, speeds_x if mixed else speeds_z, speeds_z)
        for h, v, spin, terms in zip(derivatives, velocities, SIGMA, axes, strict=True):
            check_axis_terms(terms)
            check(h == kron(v, spin), "principal coefficient from Laurent expansion")
            h2 = mul(h, h)
            check(trace(h2) == C(F(20)), "axial eigenvalue multiplicity")
            check(
                mul(add(h2, scale(C(F(-1)), I4)), add(h2, scale(C(F(-9)), I4)))
                == zero4,
                "axial squared slopes 1 and 9",
            )
            flip = kron(I2, next(p for p in SIGMA if p != spin))
            check(
                add(mul(h, flip), mul(flip, h)) == zero4,
                "both signs of axial slopes",
            )
        if mixed:
            oblique = add(derivatives[0], derivatives[1])
            oblique_square = add(mul(oblique, oblique), scale(C(F(-10)), I4))
            check(trace(oblique_square) == ZERO, "oblique eigenvalue multiplicity")
            check(
                mul(oblique_square, oblique_square) == scale(C(F(36)), I4),
                "oblique squared slopes 4 and 16",
            )
            zspin = kron(I2, sz)
            check(
                add(mul(oblique, zspin), mul(zspin, oblique)) == zero4,
                "both signs of oblique slopes",
            )
        else:
            for flavor, expected in enumerate((b, a)):
                check(
                    trace_gram(tuple(flavor_block(d, flavor) for d in derivatives))
                    == expected,
                    "each walk's derived cone Gram in the same frame",
                )
        for angles in product(phases, repeat=3):
            fx, fy, fz = (
                evolve_axis(terms, phase)
                for terms, phase in zip(axes, angles, strict=True)
            )
            u = mul(mul(fx, fy), fz)
            check(mul(u, dagger(u)) == I4, "exact walk unitarity off-grid")
            check(flavor_off_diagonal(u) == mixed, "actual flavor mixing off-grid")
            tested += 1
    return tested


def main() -> None:
    tested = check_trace_gram()
    check_basis_rotation()
    check_mass()
    walks = check_lattice_walks()
    print(f"{tested} exact determinants: trace Gram ranks 1, 2, 3, 2, 3; tilt allowed.")
    print("A spin-basis rotation preserves G; two speeds on one lattice need not.")
    print(
        f"{walks} exact walk checks: common finite support, unequal axial slopes ±1, ±3."
    )
    print("Noncommuting flavor mixing: oblique slopes ±2, ±4; no common flavor line.")
    print("Full 2-state Pauli triplet: no anticommuting mass; 4-state control: mass.")
    print("These supplied kinematics select neither dimension nor a universal metric.")


if __name__ == "__main__":
    main()
