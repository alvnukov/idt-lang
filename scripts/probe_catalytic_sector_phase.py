"""Conditional native phase kickback: exact irrational resource versus finite seed.

Supplied model: complex amplitudes, squared-norm readout, coherent address
control and identity bypass, with all six interferometer addresses carrying
the SAME total charge. The internal three-address factor is an encoding,
not a derived independent physical subsystem. Only native T_ij gates and
an explicitly accounted initial coherent herald are used in the finite
construction. No relative phase ACROSS superselection sectors is measured.

On centered V_3, D=T_12 T_01 has eigenvalues
lambda_+/-=(+/-sqrt(7)+3i)/4. A supplied eigenstate psi_+ permits exact
kickback: controlled D^k gives data phase lambda_+^k and returns that SAME
catalyst, independently of the data input. The joint operator is still
Gaussian-dyadic and respects rational coordinate blocks; its effective data
operator need not be dyadic when the supplied catalytic ray is irrational.
This does not contradict a determinant bound on the full joint operator.
The phase has infinite order: lambda_+/i has real part 3/4; if it were a
root of unity, its sum with its inverse, 3/2, would be an algebraic integer.
Consequently no positive power of lambda_+ belongs to mu_4.

Exact preparation obstruction, a field argument rather than a finite test:
a nonzero Q(i)-projective eigenvector v would give lambda_+=(Dv)_j/v_j in
Q(i), impossible. Every finite Gaussian-dyadic word or rational herald
branch preserves Q(i)-projective rays from rational-projective seeds;
normalizing a branch changes no ray. Adaptive finite branches do not evade
this, and mixing branches cannot produce a new pure ray. This excludes
exact preparation of psi_+, not arbitrarily close approximation, and does
not cover independently supplied irrational states or nonrational effects.

An explicit approximate catalyst is prepared here. A native four-port
network and coherent herald produce (1,-1,0), with probability 1/2, up to
common phase and normalization. The fixed word BABAABABABB, A=T_01,
B=T_12, yields the projective vector (-15+i,-6i,15+5i), norm square 512.
Its wrong-eigenline weight is delta=1/2-337/(256*sqrt(7)), 0<delta<1/256.
No result is fitted to measured data; this is a fixed algebraic target.

UNIFORM ERROR ARGUMENT, separate from the finite loop checks: the retained
catalyst's two eigencomponents never mix under controlled powers of D.
Any number of these calls, even interleaved with data-only unitaries, has
the form U_+ on the good component and U_- on the bad component. Relative
to ideal U_+ and the unchanged ACTUAL approximate catalyst, joint vector
error is at most 2*sqrt(delta); after tracing out the catalyst, channel
diamond distance is at most 2*delta (unhalved convention). Thus the bounds
are <1/8 and <1/128, independent of call count. The output need not be
exactly uncorrelated: this is approximate catalysis, not a repeatability
claim for a perfectly returned catalyst. Noise, arbitrary ancillary gates,
or subsequent herald conditioning are outside this bound.

For a two-path loop with exponent difference k, coherence is
f_k=(1-delta)*lambda_+^k+delta*lambda_-^k. The bright probability is
(1+Re f_k)/2, within delta of the exact-eigenstate result uniformly in k.
Identical drift on both paths cancels. Distinct paths need coherent
addressing/recombination: a which-path record removes this contrast.
Fresh independently reset approximate catalysts instead give coherence
f_1^m, not f_m; here 512 uses reduce its visibility below 1/2.

For prescribed integer link exponents, two same-endpoint path phases depend
on their exponent difference. Vertex-frame offsets telescope; common path
phase cancels. This is a conditional Wilson-loop-style invariant, not a
derivation of local gauge dynamics, charges, Gauss law, or electromagnetism.
The existing probe_phase_comparison_links.py already checks the C4 loop
and frame census. Here the new content is the irrational catalytic ray,
its finite-preparation obstruction, and the uniform-versus-fresh error.

Finite checks below use exact Q(sqrt(7),i) and integer native arithmetic.
They are not a Lean proof of the general arguments, physical realization,
probability-law derivation, or QM closure. All reported fringe rates are
conditional on the initial 1/2 herald; per-injection rates include failure.

Run: python3 -B -O -m scripts.probe_catalytic_sector_phase
"""

import sys
from fractions import Fraction as F
from pathlib import Path

if not __package__:
    sys.path.insert(0, str(Path(__file__).resolve().parents[1]))

from scripts.probe_raw_gate_reconstruction import (
    embed,
    eye,
    from_turn,
    matrix,
    mul,
    plus,
    scale,
    tr,
)

Matrix = tuple[tuple[int, ...], ...]
Vector = tuple[int, ...]
Quad = tuple[F, F]  # a+b*sqrt(7)
ComplexQuad = tuple[Quad, Quad]
QZERO: Quad = (F(0), F(0))
QONE: Quad = (F(1), F(0))
CZERO: ComplexQuad = (QZERO, QZERO)
J: Matrix = ((0, -1), (1, 0))
NATIVE = from_turn(J)
WORD = "BABAABABABB"
SEED: Vector = (-15, 1, 0, -6, 15, 5)
DELTA: Quad = (F(1, 2), F(-337, 1792))
LAMBDA_PLUS: ComplexQuad = ((F(0), F(1, 4)), (F(3, 4), F(0)))
LAMBDA_MINUS: ComplexQuad = ((F(0), F(-1, 4)), (F(3, 4), F(0)))


def need(condition: bool, reason: str) -> None:
    if not condition:
        raise ValueError(reason)


def qadd(x: Quad, y: Quad) -> Quad:
    return x[0] + y[0], x[1] + y[1]


def qscale(a: F, x: Quad) -> Quad:
    return a * x[0], a * x[1]


def qsub(x: Quad, y: Quad) -> Quad:
    return qadd(x, qscale(F(-1), y))


def qmul(x: Quad, y: Quad) -> Quad:
    a, b = x
    c, d = y
    return a * c + 7 * b * d, a * d + b * c


def qnonnegative(x: Quad) -> bool:
    a, b = x
    if a >= 0 and b >= 0:
        return True
    if a <= 0 and b <= 0:
        return False
    return a * a >= 7 * b * b if a >= 0 else 7 * b * b >= a * a


def cadd(x: ComplexQuad, y: ComplexQuad) -> ComplexQuad:
    return qadd(x[0], y[0]), qadd(x[1], y[1])


def cscale(a: Quad, x: ComplexQuad) -> ComplexQuad:
    return qmul(a, x[0]), qmul(a, x[1])


def cmul(x: ComplexQuad, y: ComplexQuad) -> ComplexQuad:
    return qsub(qmul(x[0], y[0]), qmul(x[1], y[1])), qadd(
        qmul(x[0], y[1]), qmul(x[1], y[0])
    )


def cnorm(x: ComplexQuad) -> Quad:
    return qadd(qmul(x[0], x[0]), qmul(x[1], x[1]))


def rational_complex(real: F, imag: F) -> ComplexQuad:
    return (real, F(0)), (imag, F(0))


def apply(a: Matrix, x: Vector) -> Vector:
    return tuple(sum(u * v for u, v in zip(row, x, strict=True)) for row in a)


def norm_square(x: Vector) -> int:
    return sum(value * value for value in x)


def inner(x: Vector, y: Vector, denominator: int) -> ComplexQuad:
    real = sum(u * v for u, v in zip(x, y, strict=True))
    imag = sum(x[i] * y[i + 1] - x[i + 1] * y[i] for i in range(0, len(x), 2))
    return rational_complex(F(real, denominator), F(imag, denominator))


def eigen_control() -> Matrix:
    d = mul(embed(3, (1, 2), NATIVE), embed(3, (0, 1), NATIVE))  # 4*D
    need(mul(tr(d), d) == scale(16, eye(6)), "D is unitary after raw scaling")
    eigenvector: tuple[ComplexQuad, ...] = (
        rational_complex(F(2), F(-2)),
        ((F(-2), F(1)), (F(1), F(0))),
        ((F(0), F(-1)), (F(1), F(0))),
    )
    total = CZERO
    for value in eigenvector:
        total = cadd(total, value)
    need(total == CZERO, "eigenray is centered")
    for row in range(3):
        image = CZERO
        for col in range(3):
            coefficient = rational_complex(
                F(d[2 * row][2 * col], 4), F(d[2 * row + 1][2 * col], 4)
            )
            image = cadd(image, cmul(coefficient, eigenvector[col]))
        need(
            image == cmul(LAMBDA_PLUS, eigenvector[row]), "explicit irrational eigenray"
        )
    need(cnorm(LAMBDA_PLUS) == cnorm(LAMBDA_MINUS) == QONE, "unit-modulus eigenvalues")
    need(LAMBDA_PLUS[0][1] != 0, "eigenvalue not in Q(i)")
    need(
        LAMBDA_MINUS == ((F(0), F(-1, 4)), LAMBDA_PLUS[1]),
        "quadratic field conjugation exchanges eigenvalues",
    )
    return d


def native_seed(d: Matrix) -> None:
    source: Vector = (1, 0, 0, 0, 0, 0, 0, 0)
    state = source
    for edge in ((0, 1), (0, 2), (1, 3)):
        state = apply(embed(4, edge, NATIVE), state)
    need(state == (0, 4, 4, 0, 4, 0, 0, -4), "native four-port herald source")
    retained = state[:2] + state[6:8]
    need(
        F(norm_square(retained), norm_square(state)) == F(1, 2),
        "initial success probability",
    )
    # Retained ports 0,3 are i*(1,-1)/2; append an empty third address.
    # The common i and normalization do not change a projective ray.
    initial: Vector = (1, 0, -1, 0, 0, 0)
    prepared = initial
    for letter in WORD:
        prepared = apply(
            embed(3, (0, 1) if letter == "A" else (1, 2), NATIVE), prepared
        )
    need(prepared == tuple(128 * value for value in SEED), "fixed native seed word")
    need(norm_square(SEED) == 512, "seed normalization")
    uniform = matrix(6, lambda i, j: int(i % 2 == j % 2))
    need(apply(uniform, SEED) == (0,) * 6, "seed has no uniform eigencomponent")
    h12 = plus(scale(3, plus(d, tr(d))), scale(-8, uniform))
    centered = plus(scale(3, eye(6)), uniform, -1)
    need(
        mul(h12, h12) == scale(84, centered),
        "H squared fixes the two spectral projectors",
    )
    numerator = sum(x * y for x, y in zip(SEED, apply(h12, SEED), strict=True))
    need(F(numerator, 12 * norm_square(SEED)) == F(337, 256), "spectral mean of H")
    need(
        qnonnegative(DELTA) and DELTA != QZERO,
        "strictly positive wrong-eigenline weight",
    )
    need(qnonnegative(qsub((F(1, 256), F(0)), DELTA)), "delta at most 1/256")
    need(337**2 < 7 * 128**2 and 337**2 > 7 * 127**2, "strict rational squared bounds")


def spectral_loops(d: Matrix) -> tuple[F, F]:
    vector = SEED
    lp = lm = rational_complex(F(1), F(0))
    error_bound = qscale(F(4), qmul(DELTA, DELTA))
    for k in range(65):
        observed = inner(SEED, vector, 512 * 4**k)
        predicted = cadd(cscale(qsub(QONE, DELTA), lp), cscale(DELTA, lm))
        need(observed == predicted, "exact rational/spectral coherence identity")
        error = cadd(observed, cscale((F(-1), F(0)), lp))
        spectral_difference = cadd(lm, cscale((F(-1), F(0)), lp))
        joint_residual = qmul(DELTA, cnorm(spectral_difference))
        need(
            qnonnegative(qsub(qscale(F(4), DELTA), joint_residual)),
            "unchanged-actual-catalyst vector error squared <=4*delta",
        )
        need(
            qnonnegative(qsub(error_bound, cnorm(error))),
            "uniform coherence error <=2*delta",
        )
        probability_error = qscale(F(1, 2), error[0])
        need(
            qnonnegative(
                qsub(qmul(DELTA, DELTA), qmul(probability_error, probability_error))
            ),
            "uniform fringe error <=delta",
        )
        vector = apply(d, vector)
        lp, lm = cmul(lp, LAMBDA_PLUS), cmul(lm, LAMBDA_MINUS)
    one = inner(SEED, apply(d, SEED), 512 * 4)
    need(one == rational_complex(F(337, 512), F(3, 4)), "one-loop coherence")
    squared_visibility = cnorm(one)
    need(
        squared_visibility == (F(261025, 262144), F(0)),
        "fresh-catalyst visibility factor",
    )
    need(squared_visibility[0] ** 512 < F(1, 4), "fresh 512-use visibility below 1/2")
    return one[0][0], one[1][0]


def interferometer(
    k: int, *, flagged: bool = False, common: bool = False
) -> tuple[F, F]:
    """Six same-charge addresses; exact raw numerators and native call count."""
    state = SEED + (0,) * 6
    count = 0
    splitter = ((0, 3), (1, 4), (2, 5))
    for edge in splitter:
        state = apply(embed(6, edge, NATIVE), state)
        count += 1
    branches = [state] if not flagged else [state[:6] + (0,) * 6, (0,) * 6 + state[6:]]
    for _ in range(k):
        for edge in ((0, 1), (1, 2), (3, 4), (4, 5)) if common else ((3, 4), (4, 5)):
            branches = [apply(embed(6, edge, NATIVE), branch) for branch in branches]
            count += 1
    for edge in reversed(splitter):
        for _ in range(3):
            branches = [apply(embed(6, edge, NATIVE), branch) for branch in branches]
            count += 1
    denominator = 512 * 4**count
    return F(sum(norm_square(x[:6]) for x in branches), denominator), F(
        sum(norm_square(x[6:]) for x in branches), denominator
    )


def readout_controls(d: Matrix) -> None:
    vector = SEED
    for k in range(9):
        coherence = inner(SEED, vector, 512 * 4**k)
        bright, dark = interferometer(k)
        need(
            bright == (1 + coherence[0][0]) / 2 and bright + dark == 1,
            "same-charge coherent fringe",
        )
        need(
            interferometer(k, flagged=True) == (F(1, 2), F(1, 2)),
            "no coherent address comparison",
        )
        need(
            interferometer(k, common=True) == (F(1), F(0)),
            "common branch phase cancels",
        )
        vector = apply(d, vector)
    need(
        interferometer(1) == (F(849, 1024), F(175, 1024)),
        "one-loop approximate native fringe",
    )
    need(
        sum((F(849, 2048), F(175, 2048), F(1, 2))) == 1,
        "per-injection herald accounting",
    )
    # Same-endpoint exponent differences survive vertex frame offsets;
    # this integer identity is not a supplied dynamical law for the links.
    links = (2, -1, 3, 4)  # 0->1->3 versus 0->2->3
    for frame in ((0, 0, 0, 0), (1, -2, 5, 3), (-3, 4, -1, 2)):
        a, b, c, e = links
        rebased = (
            a + frame[1] - frame[0],
            b + frame[3] - frame[1],
            c + frame[2] - frame[0],
            e + frame[3] - frame[2],
        )
        need(
            rebased[0] + rebased[1] - rebased[2] - rebased[3] == a + b - c - e,
            "same-endpoint loop exponent invariant",
        )


def main() -> None:
    d = eigen_control()
    native_seed(d)
    spectral_loops(d)
    readout_controls(d)
    print(
        "Exact eigenray has eigenvalue (sqrt(7)+3i)/4 outside Q(i); finite rational-projective preparation cannot produce it exactly."
    )
    print(
        f"Native approximate seed: {WORD}; delta=1/2-337/(256*sqrt(7)), strictly between 0 and 1/256; initial herald 1/2."
    )
    print(
        "Retained-catalyst bounds: joint vector error <1/8, data diamond error <1/128, fringe error <1/256, uniform in coherent loop count."
    )
    print(
        "Exact spectral checks k=0..64; native same-charge fringes k=0..8. One-loop return: 849/1024 per herald, 849/2048 per injection."
    )
    print(
        "Controls: fresh 512-use visibility <1/2; which-path record gives 1/2; common drift gives unit return."
    )
    print(
        "No cross-superselection phase measurement, independent physical catalyst, local gauge dynamics, or QM derivation is asserted."
    )


if __name__ == "__main__":
    main()
