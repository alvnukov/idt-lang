"""Real oriented-cell reciprocal shears: a conditional wave primitive, not Maxwell derived.

LOWER INPUTS. Supply an oriented periodic cubic cell complex, real signed
cochains, a clock, and reciprocal local shears. Incidence gives G=d0, C=d1,
D=d2 with CG=DC=0. E is a PRIMAL EDGE cochain and B a PRIMAL FACE cochain.
Electric flux is on dual faces, magnetic effort on dual edges. Identifying
their stored coordinates with E and B uses positive Hodge maps; it is not
another incidence identity. The unit cubic Hodge is an explicit choice here.
No preassigned internal i, quantum state, measurement, or Born rule is used.

UPDATE. On staggered times use B'=B-h*C*E, E'=E+h*C^T*B'. These two shears
are local, invertible in reverse order, determinant one, and preserve the
FULL Gauss values G^T E and D B. Their exact invariant is
 Q(E,B)=||E||^2+||B||^2-h <B,C E>,
not the unmodified sum of squares. It is positive iff h^2 lambda_max(C^T C)<4.
On the cubic lattice lambda_max<=12; h=1/2 is strictly stable. The elementary
bound ||C||<=sqrt(12)<7/2 gives (1/8)||X||^2 <= Q <= (15/8)||X||^2,
so all powers obey ||S^n X||^2 <=15||X||^2. No complex phase is needed for
bounded real oscillation. A common sign convention chooses h>0. More generally
reciprocal coefficients a,b require ab>0 for nontrivial stable oscillators;
opposite signs give hyperbolicity, and a single nonzero shear is unbounded.

MODES. In staggered geometric Fourier frames, s_j=2 sin(k_j/2) and the curl
has C* C=|s|^2 I-s s^T. Fourier i is an analysis convention for real shifts,
not a newly supplied scalar particle. At nonzero momentum there are TWO
transverse oscillator polarizations, each with
 cos(omega)=1-h^2 |s|^2/2,
 sin^2(omega/2)=h^2 sum_j sin^2(k_j/2).
The two longitudinal E/B coordinates are static Gauss data; imposing zero
Gauss values removes them, rather than the dynamics damping/projecting them.
At zero momentum all six uniform harmonic coordinates are static. This is
a classical linear wave carrier, not a derivation of two quantum particles.
The leading speed is isotropic for the supplied cubic metric, but the quartic
term contains sum k_j^4 and is not rotationally isotropic at all wavelengths.

CFL/INTEGER WALL. At h=1 the corner (pi,pi,pi) has lambda=12 and oscillator
trace -10, hence a reciprocal hyperbolic eigenvalue pair. At h^2 lambda=4 the
double eigenvalue -1 has a nonzero nilpotent part: generic powers grow
linearly. Thus CFL equality is not power-bounded on a grid containing that
mode. Strictness for all momenta is h<1/sqrt(3); finite odd grids may have a
smaller spectral maximum. Integer nonzero unit reciprocal coefficients fail
this particular full-cubic ansatz. Rescaling E and B changes a,b but not ab,
so cannot make both stable positive coefficients integers. This is NOT a
no-go for other integer cellular/permutation wave dynamics.

EXACT RESOLUTION IS A RESOURCE. h=1/2 gives dyadic determinant-one shears,
invertible over Z[1/2], not integer automorphisms of one fixed stock lattice.
After t steps a common denominator 4^t suffices. It is sometimes necessary:
on a 3-cell periodic direction the real integer profile (2,-1,-1) has
lambda=3, and its mode matrix S=[[1/4,3/2],[-1/2,1]]. For 4S modulo2 the only
nonzero entry is (0,0), so (S^t)00 has denominator exactly 4^t for every t.
Stable amplitude bounds therefore do not imply fixed exact digital resolution.
Finite-horizon scaled stocks and indefinitely fixed-resolution dynamics differ.
Moreover these shears are not Euclidean orthogonal. Dyadic coefficients alone
do not compile them from the existing lossless G/T junction gates on the same
coordinate carrier. A shear primitive, alternative encoding, interactions,
or an enlarged carrier remains an additional obligation.

COUNTERCONTROLS. Incidence conservation also allows identity and local curl-
Laplacian diffusion. It does not select reciprocal waves. -S preserves the
SOURCE-FREE divergence kernels and moves the small-k Floquet phase to pi,
but flips nonzero Gauss densities. It is not an equally charge-conserving map.
Indeed any continuous translation-invariant map preserving both arbitrary
Gauss values has S(0)=I: divide L(k)S(k)=L(k) by k along each coordinate axis.
Thus a nonzero zero-momentum gap needs weakened conservation or extra fields.
Positive anisotropic Hodge weights also preserve the incidence identities;
magnetic weights (1,1,4) give transverse speed ratio2 for a wave along x.
Topology neither selects that metric nor excludes it. No physical speed,
electromagnetic constitutive law, source coupling, or Maxwell ontology follows.

This route avoids the four-leg longitudinal-mode identification and Weyl-pair
complexification issues by changing the primitive carrier to oriented cells.
That new carrier, clock, Hodge choice, reciprocal sign, stable time step, and
exact-resolution resource are exposed inputs, not consequences of those routes.
The executable checks are exact finite algebra, not Lean proofs. External
literature was not verified because the web-search endpoint was unavailable.
"""

from __future__ import annotations

import json
import sys
from fractions import Fraction as F
from itertools import product
from pathlib import Path

if not __package__:
    sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
from scripts import probe_balanced_phase_composition as b

Cell = tuple[int, int, int]


def need(ok: bool, why: str) -> None:
    if not ok:
        raise ArithmeticError(why)


def sub(a: b.Matrix, c: b.Matrix) -> b.Matrix:
    return b.add(a, b.scale(-1, c))


def zero(rows: int, columns: int) -> b.Matrix:
    return b.matrix(tuple((0,) * columns for _ in range(rows)))


def blocks(a: b.Matrix, c: b.Matrix, d: b.Matrix, e: b.Matrix) -> b.Matrix:
    return tuple(x + y for x, y in zip(a, c, strict=True)) + tuple(
        x + y for x, y in zip(d, e, strict=True)
    )


def rank(a: b.Matrix) -> int:
    rows = [list(row) for row in a]
    pivot = 0
    for column in range(len(a[0])):
        selected = next((i for i in range(pivot, len(rows)) if rows[i][column]), None)
        if selected is None:
            continue
        rows[pivot], rows[selected] = rows[selected], rows[pivot]
        divisor = rows[pivot][column]
        rows[pivot] = [x / divisor for x in rows[pivot]]
        for i in range(pivot + 1, len(rows)):
            factor = rows[i][column]
            if factor:
                rows[i] = [
                    x - factor * y for x, y in zip(rows[i], rows[pivot], strict=True)
                ]
        pivot += 1
    return pivot


def incidence(n: int) -> tuple[b.Matrix, b.Matrix, b.Matrix, b.Matrix]:
    """Forward oriented boundaries; adjoints are NOT guessed backward curls."""
    cells: tuple[Cell, ...] = tuple(
        (x, y, z) for x, y, z in product(range(n), repeat=3)
    )
    count, size = len(cells), 3 * len(cells)
    lookup = {cell: i for i, cell in enumerate(cells)}

    def forward(cell: Cell, axis: int) -> Cell:
        values = list(cell)
        values[axis] = (values[axis] + 1) % n
        return values[0], values[1], values[2]

    gradient = [[0] * count for _ in range(size)]
    curl = [[0] * size for _ in range(size)]
    divergence = [[0] * size for _ in range(count)]
    scalar_lap = [[0] * count for _ in range(count)]
    for cell in cells:
        x = lookup[cell]
        for axis in range(3):
            y = lookup[forward(cell, axis)]
            gradient[3 * x + axis][y] += 1
            gradient[3 * x + axis][x] -= 1
            divergence[x][3 * y + axis] += 1
            divergence[x][3 * x + axis] -= 1
            # Sum of incidence outer products, one per oriented edge.
            scalar_lap[x][x] += 1
            scalar_lap[y][y] += 1
            scalar_lap[x][y] -= 1
            scalar_lap[y][x] -= 1
            j, k = (axis + 1) % 3, (axis + 2) % 3
            curl[3 * x + axis][3 * lookup[forward(cell, j)] + k] += 1
            curl[3 * x + axis][3 * x + k] -= 1
            curl[3 * x + axis][3 * lookup[forward(cell, k)] + j] -= 1
            curl[3 * x + axis][3 * x + j] += 1
    return (
        b.matrix(gradient),
        b.matrix(curl),
        b.matrix(divergence),
        b.matrix(scalar_lap),
    )


def incidence_controls(n: int) -> tuple[b.Matrix, b.Matrix, b.Matrix]:
    g, c, d, lap = incidence(n)
    count, size = n**3, 3 * n**3
    need(b.multiply(c, g) == zero(size, count), "curl of gradient")
    need(b.multiply(d, c) == zero(count, size), "divergence of curl")
    vector_lap = b.matrix(
        tuple(
            tuple(lap[i // 3][j // 3] if i % 3 == j % 3 else 0 for j in range(size))
            for i in range(size)
        )
    )
    need(
        b.add(b.multiply(b.transpose(c), c), b.multiply(g, b.transpose(g)))
        == vector_lap,
        "curl-gradient Laplacian decomposition",
    )
    need(rank(g) == rank(d) == count - 1, "periodic scalar incidence ranks")
    need(rank(c) == 2 * (count - 1), "two transverse directions per nonzero momentum")
    return g, c, d


def update(c: b.Matrix, h: F) -> tuple[b.Matrix, b.Matrix, b.Matrix]:
    size = len(c)
    eye, ct = b.identity(size), b.transpose(c)
    s = blocks(
        sub(eye, b.scale(h * h, b.multiply(ct, c))), b.scale(h, ct), b.scale(-h, c), eye
    )
    inverse = blocks(
        eye, b.scale(-h, ct), b.scale(h, c), sub(eye, b.scale(h * h, b.multiply(c, ct)))
    )
    energy = blocks(eye, b.scale(-h / 2, ct), b.scale(-h / 2, c), eye)
    return s, inverse, energy


def finite_update_controls(g: b.Matrix, c: b.Matrix, d: b.Matrix) -> dict[str, object]:
    h, size, count = F(1, 2), len(c), len(d)
    s, inverse, energy = update(c, h)
    integer_s, integer_inverse, _ = update(c, F(1))
    need(
        all(
            x.denominator == 1
            for a in (integer_s, integer_inverse)
            for row in a
            for x in row
        ),
        "integer unit step and inverse are integral",
    )
    need(
        b.multiply(s, inverse) == b.identity(2 * size),
        "exact inverse reciprocal shears",
    )
    need(
        b.multiply(b.transpose(s), b.multiply(energy, s)) == energy,
        "modified energy invariant",
    )
    need(
        b.multiply(b.transpose(s), s) != b.identity(2 * size),
        "not a native Euclidean-orthogonal word",
    )
    gauss = blocks(b.transpose(g), zero(count, size), zero(count, size), d)
    need(b.multiply(gauss, s) == gauss, "both full Gauss values conserved")
    # Triangular factors have all diagonal entries one, certifying determinant
    # one without an expensive large determinant expansion.
    eye, z = b.identity(size), zero(size, size)
    first = blocks(eye, z, b.scale(-h, c), eye)
    second = blocks(eye, b.scale(h, b.transpose(c)), z, eye)
    need(b.multiply(second, first) == s, "unit-diagonal shear factorization")
    for factor in (first, second):
        need(all(factor[i][i] == 1 for i in range(2 * size)), "unit shear diagonal")
    need(
        F(12) < F(7, 2) ** 2 and 1 - h * F(7, 2) / 2 == F(1, 8),
        "strict rational energy bound",
    )
    # Topological conservation does not select an oscillatory dynamics.
    nu = F(1, 16)
    diffuse = blocks(
        sub(eye, b.scale(nu, b.multiply(b.transpose(c), c))),
        z,
        z,
        sub(eye, b.scale(nu, b.multiply(c, b.transpose(c)))),
    )
    need(b.multiply(gauss, diffuse) == gauss, "diffusion also preserves Gauss values")
    need(
        b.multiply(b.transpose(diffuse), diffuse) != b.identity(2 * size),
        "diffusion is not lossless",
    )
    negative = b.scale(-1, s)
    need(
        b.multiply(gauss, negative) == b.scale(-1, gauss),
        "gapped sign control flips charges",
    )
    need(b.multiply(gauss, negative) != gauss, "source-free preservation is weaker")
    return {
        "real_state_dimension": 2 * size,
        "time_step": str(h),
        "determinant": 1,
        "exact_energy": "E.E+B.B-h B.CE",
        "energy_bounds": ["1/8", "15/8"],
        "squared_norm_power_bound": 15,
        "native_orthogonal_gate_compilation": "not supplied: the update is not Euclidean orthogonal",
        "alternatives": [
            "identity",
            "curl-Laplacian diffusion with nu=1/16",
            "-S preserves only source-free kernels, not nonzero charge values",
        ],
    }


def cross(v: tuple[int, int, int]) -> b.Matrix:
    x, y, z = v
    return b.matrix(((0, -z, y), (z, 0, -x), (-y, x, 0)))


def oscillator(lam: F, a: F, coefficient_b: F) -> b.Matrix:
    # Coordinates E=x*e, B=y*C*e, where C^T C e=lam*e.
    return b.matrix(((1 - a * coefficient_b * lam, coefficient_b * lam), (-a, 1)))


def mode_controls() -> dict[str, object]:
    for v in product((-1, 0, 1), repeat=3):
        vector = (v[0], v[1], v[2])
        k = cross(vector)
        lam = sum(x * x for x in v)
        outer = b.matrix(tuple(tuple(x * y for y in v) for x in v))
        need(
            b.multiply(b.transpose(k), k) == sub(b.scale(lam, b.identity(3)), outer),
            "transverse symbol identity",
        )
        need(rank(k) == (2 if lam else 0), "two polarizations, not three")
    for eigenvalue in (F(3), F(4), F(8), F(12)):
        s = oscillator(eigenvalue, F(1, 2), F(1, 2))
        need(
            b.determinant(s) == 1 and b.trace(s) == 2 - eigenvalue / 4,
            "transverse oscillator dispersion",
        )
        need(abs(b.trace(s)) < 2, "strict half-step stability")
    unit = oscillator(F(12), F(1), F(1))
    need(
        b.trace(unit) == -10 and b.determinant(unit) == 1,
        "integer unit UV hyperbolicity",
    )
    critical = oscillator(F(4), F(1), F(1))
    nilpotent = b.add(critical, b.identity(2))
    need(
        nilpotent != zero(2, 2) and b.multiply(nilpotent, nilpotent) == zero(2, 2),
        "CFL equality Jordan block",
    )
    power = b.identity(2)
    for n in range(1, 9):
        power = b.multiply(critical, power)
        need(
            power == b.scale((-1) ** n, sub(b.identity(2), b.scale(n, nilpotent))),
            "linear critical growth",
        )
    opposite = oscillator(F(3), F(1, 2), F(-1, 2))
    need(b.trace(opposite) > 2, "opposite reciprocal signs are unstable")
    shear = oscillator(F(3), F(0), F(1))
    need(
        b.multiply(sub(shear, b.identity(2)), sub(shear, b.identity(2))) == zero(2, 2)
        and shear != b.identity(2),
        "one-way shear has linear growth",
    )
    # Equal Cartesian lengths, different quartic lattice corrections.
    directions = ((5, 0, 0), (3, 4, 0))
    quadratic = tuple(sum(x * x for x in v) for v in directions)
    quartic = tuple(-F(sum(x**4 for x in v), 12) for v in directions)
    need(
        quadratic == (25, 25) and quartic[0] - quartic[1] == -24,
        "first-order isotropy is not all-wave isotropy",
    )
    # Positive Hodge data change the two transverse branches without changing
    # the incidence symbol. Along x, the y/z effort modes see weights4/1.
    k = cross((1, 0, 0))
    magnetic_hodge = b.matrix(((1, 0, 0), (0, 1, 0), (0, 0, 4)))
    anisotropic = b.multiply(b.transpose(k), b.multiply(magnetic_hodge, k))
    need(
        anisotropic == b.matrix(((0, 0, 0), (0, 4, 0), (0, 0, 1))),
        "metric ambiguity splits transverse speeds",
    )
    return {
        "nonzero_momentum": "two transverse oscillators plus two static Gauss coordinates",
        "zero_momentum": "six static harmonic coordinates",
        "dispersion": "sin^2(omega/2)=h^2 sum_j sin^2(k_j/2)",
        "integer_unit_corner_trace": -10,
        "CFL_equality": "nontrivial -1 Jordan block; linear growth",
        "equal_length_quartic_difference": "-24",
        "positive_anisotropic_Hodge_speed_ratio": 2,
    }


def resolution_control(g: b.Matrix, c: b.Matrix, d: b.Matrix) -> dict[str, object]:
    # A real, integer, divergence-free mode on the n=3 torus, along x with
    # electric direction y. No Fourier complex scalar is needed to prepare it.
    cells = tuple(product(range(3), repeat=3))
    e = b.matrix(
        tuple(
            (2 if cell[0] == 0 else -1,) if axis == 1 else (0,)
            for cell in cells
            for axis in range(3)
        )
    )
    ce = b.multiply(c, e)
    need(
        b.multiply(b.transpose(g), e) == zero(len(g[0]), 1),
        "source-free real electric profile",
    )
    need(b.multiply(d, ce) == zero(len(d), 1), "source-free real magnetic profile")
    need(
        b.multiply(b.transpose(c), ce) == b.scale(3, e),
        "integer transverse lambda-three profile",
    )
    s = oscillator(F(3), F(1, 2), F(1, 2))
    need(s == b.matrix(((F(1, 4), F(3, 2)), (F(-1, 2), 1))), "resolution witness")
    numerator = b.scale(4, s)
    mod_two = tuple(tuple(int(x) % 2 for x in row) for row in numerator)
    need(mod_two == ((1, 0), (0, 0)), "idempotent numerator residue")
    power = b.identity(2)
    electric, magnetic = e, zero(len(e), 1)
    for t in range(1, 9):
        power = b.multiply(s, power)
        magnetic = sub(magnetic, b.scale(F(1, 2), b.multiply(c, electric)))
        electric = b.add(
            electric, b.scale(F(1, 2), b.multiply(b.transpose(c), magnetic))
        )
        need(
            electric == b.scale(power[0][0], e)
            and magnetic == b.scale(power[1][0], ce),
            "full cochain update matches real mode",
        )
        need(power[0][0].denominator == 4**t, "exact growing dyadic denominator")
        need(
            max(row[0].denominator for row in electric) == 4**t,
            "denominator is present in actual edge coordinates",
        )
    # At every step the residue (4S)^t mod2 is the same nonzero projector;
    # hence the denominator statement holds for every t, not only this prefix.
    return {
        "mode_lambda": 3,
        "exact_denominator_after_t": "4^t",
        "extra_fractional_bits_per_tick": 2,
        "bounded_checks": 8,
        "boundary": "bounded amplitudes, unbounded exact resolution demand on this mode",
    }


def main() -> None:
    small = incidence_controls(2)
    large = incidence_controls(3)
    result = {
        "status": "conditional oriented-cell wave primitive; no Maxwell or QM derivation",
        "incidence_ranks": {
            "n2": {"G": 7, "C": 14, "D": 7},
            "n3": {"G": 26, "C": 52, "D": 26},
        },
        "reciprocal_update": finite_update_controls(*small),
        "modes_and_countercontrols": mode_controls(),
        "exact_resolution": resolution_control(*large),
        "inputs_not_derived": [
            "oriented cell carrier",
            "signed real cochains",
            "clock",
            "positive Hodge identification",
            "reciprocal shear law",
            "stable time step",
            "exact dyadic resolution",
        ],
    }
    print(json.dumps(result, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
