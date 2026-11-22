"""Three matched-axis source-parity settings, WITH trusted calibration.

Supply two independent sources, real symmetric endpoint reflections A_i,C_i
in the real null, complete outputs, and ONE setting-independent Bob instrument.
Bob may instead finish before a fresh axis choice. Broadcasting that choice to
Bob changes the model. Write sigma_b for the unnormalized outer states, with
sum sigma_b real separable (independent sources suffice). Four reported signs
s(b) have product -1. The all-output score is
  M = sum_{b,i} s_i(b) Tr[(A_i tensor C_i) sigma_b].
There are three matched settings and 16 outcomes each, not Renou's uncalibrated
functional. The dimension-independent bound is conditional on calibration,
not device-independent.

EXACT CALIBRATION. Pairwise anticommutation at BOTH endpoints makes K_i=A_i
tensor C_i commuting reflections. L=K_1 K_2 K_3 has eigenvalues +/-1, and
H_b=sum s_i K_i <= 2I-L: the signed eigenvalue product is -L. The local triple
products P=A_1 A_2 A_3 and Q=C_1 C_2 C_3 are real skew-symmetric. Hence every
real separable unconditional outer state has Tr(L rho)=0, giving M<=2.
The explicit real Phi4-source control below attains 2 with a positive complete
Bob measurement. Complex Phi2 sources and the existing native Pauli controls
give 3 on all 48 cells, without Charlie's oblique analyzer or a third logical
blank path. Paired-rail encoding, sources and squared-amplitude readout remain
supplied; this does not derive those resources or a probability rule.

ROBUST CALIBRATION, no commutation of K_i required. Put U_i=s_i K_i and
V_i=U_1...U_{i-1}(I-U_i). Then sum V_i=I+L and
  sum_{i<j}(V_i-V_j)^*(V_i-V_j) = 16I-6H_b-L-L^* >= 0.
Thus M<=8/3-Tr[sym(L)rho]/3 <= 8/3+e_A e_C/3, where
e_A=||sym(P)||, e_C=||sym(Q)||. Real-separable factorization is essential.
The identity P+P^*=A{B,C}-{A,C}B+C{A,B} gives
e_A<=min(1, (||{A,B}||+||{A,C}||+||{B,C}||)/2), and similarly for C.
One exactly skew triple therefore suffices for a nontrivial robust bound.

GEOMETRIC SHARPENING (analytical argument, not a Lean proof). For a pure
branch let t=Re<Psi,L Psi>, beta_i=arccos<Psi,U_i Psi>. The unit-sphere path
Psi,U_1 Psi,U_1 U_2 Psi,U_1 U_2 U_3 Psi has successive angles beta_i and
endpoint angle alpha=arccos(-t)<=pi. Hence sum beta_i>=alpha. First shorten
the beta_i coordinatewise to gamma_i with sum alpha. Cosine decreases on
[0,pi], so this can only increase the score. Every pair of gamma angles sums
to at most pi; replacing a pair by its mean increases its cosine sum because
cos a+cos b=2 cos((a+b)/2) cos((a-b)/2), with the first cosine nonnegative.
Repeated max/min averaging converges to alpha/3. This proves the needed bound
without falsely assuming global concavity of cosine on [0,pi]. Therefore
  M_branch <= f(t) = 3 cos(arccos(-t)/3).
On y=f(t) in [3/2,3], t=y-4y^3/27; inverse differentiation gives f decreasing
and concave, including endpoints by continuity. Jensen over all pure branches
then gives M<=3 cos(arccos(e_A e_C)/3). A convenient supporting tangent is
M<=(3 sqrt(3)+e_A e_C)/2, also capped by the algebraic bound 3. In particular,
one skew side gives 3 sqrt(3)/2 < 13/5 < 8/3. This sharpening is not claimed
optimal for the independent-source network. Finite rational reflection controls
below saturate the geometric step, not the calibrated network bound.

CALIBRATION WALL. Since P is orthogonal/unitary,
||sym(P)||=||P^2+I||/2. A reversible double-triple loop compared coherently
against -I can calibrate this quantity only with trusted gate composition,
phase-sensitive reference control and coverage of the occupied hidden support.
Phase-blind return cannot distinguish I from -I. A few tested preparation rays
do not certify an operator norm on an unknown larger carrier. The hidden-block
control passes the chosen calibrated block but reaches M=3 on an untested block.
Commuting axes and setting-dependent Bob instruments give separate M=3 cheats.
No empirical separation, shot-level significance, new public status, Born/QM
derivation, or SDP/Lean certificate is supplied by this exact finite probe.
"""

from __future__ import annotations

import sys
from fractions import Fraction as F
from itertools import combinations, product
from pathlib import Path

if not __package__:
    sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
from scripts.gaussian_dyadic_words import eye as gaussian_eye
from scripts.gaussian_dyadic_words import run, synthesize
from scripts.probe_two_source_phase_network import (
    AXES,
    bell_ket,
    cliffords,
    effect,
    gram,
    network_probability,
    turned,
)
from scripts.probe_two_source_phase_network import (
    Z as COMPLEX_Z,
)

Matrix = tuple[tuple[F, ...], ...]
Triple = tuple[Matrix, Matrix, Matrix]
Signs = tuple[int, int, int]
SIGNS: tuple[Signs, ...] = tuple((a, b, -a * b) for a, b in product((-1, 1), repeat=2))


def need(ok: bool, reason: str) -> None:
    if not ok:
        raise ArithmeticError(reason)


def eye(n: int) -> Matrix:
    return tuple(tuple(F(i == j) for j in range(n)) for i in range(n))


def scale(c: F | int, a: Matrix) -> Matrix:
    return tuple(tuple(c * x for x in row) for row in a)


def add(a: Matrix, b: Matrix) -> Matrix:
    return tuple(
        tuple(x + y for x, y in zip(ar, br, strict=True))
        for ar, br in zip(a, b, strict=True)
    )


def transpose(a: Matrix) -> Matrix:
    return tuple(zip(*a, strict=True))


def multiply(a: Matrix, b: Matrix) -> Matrix:
    return tuple(
        tuple(
            sum((x * y for x, y in zip(row, column, strict=True)), F(0))
            for column in zip(*b, strict=True)
        )
        for row in a
    )


def kron(a: Matrix, b: Matrix) -> Matrix:
    return tuple(tuple(x * y for x in ar for y in br) for ar in a for br in b)


def trace(a: Matrix) -> F:
    return sum((a[i][i] for i in range(len(a))), F(0))


def triple_product(axes: Triple) -> Matrix:
    return multiply(multiply(axes[0], axes[1]), axes[2])


def symmetric(a: Matrix) -> Matrix:
    return scale(F(1, 2), add(a, transpose(a)))


def anticommutator(a: Matrix, b: Matrix) -> Matrix:
    return add(multiply(a, b), multiply(b, a))


I2 = eye(2)
Z: Matrix = ((F(1), F(0)), (F(0), F(-1)))
X: Matrix = ((F(0), F(1)), (F(1), F(0)))
J: Matrix = ((F(0), F(-1)), (F(1), F(0)))
REAL_AXES: Triple = (kron(Z, I2), kron(X, I2), kron(J, J))


def reflection_controls(axes: Triple) -> None:
    identity = eye(len(axes[0]))
    for a in axes:
        need(transpose(a) == a and multiply(a, a) == identity, "symmetric reflection")
    a, b, c = axes
    p = triple_product(axes)
    rhs = add(
        add(
            multiply(a, anticommutator(b, c)),
            scale(-1, multiply(anticommutator(a, c), b)),
        ),
        multiply(c, anticommutator(a, b)),
    )
    need(add(p, transpose(p)) == rhs, "pair-error to triple-error identity")
    loop = add(multiply(p, p), identity)
    sym = symmetric(p)
    need(
        multiply(transpose(loop), loop) == scale(4, multiply(sym, sym)),
        "phase-sensitive double-loop calibration identity",
    )


def robust_sos(ks: Triple, signs: Signs) -> None:
    identity = eye(len(ks[0]))
    zero = scale(0, identity)
    prefix, h = identity, zero
    vectors = []
    for sign, k in zip(signs, ks, strict=True):
        u = scale(sign, k)
        vectors.append(multiply(prefix, add(identity, scale(-1, u))))
        prefix = multiply(prefix, u)
        h = add(h, u)
    l = triple_product(ks)
    need(prefix == scale(-1, l), "odd Bell-sign parity")
    sos = zero
    for left, right in combinations(vectors, 2):
        difference = add(left, scale(-1, right))
        sos = add(sos, multiply(transpose(difference), difference))
    expected = add(
        add(scale(16, identity), scale(-6, h)), scale(-1, add(l, transpose(l)))
    )
    need(sos == expected, "exact positive sum-of-squares robustness certificate")


def joint_axes(left: Triple, right: Triple) -> Triple:
    return kron(left[0], right[0]), kron(left[1], right[1]), kron(left[2], right[2])


def real_sharp_control() -> F:
    reflection_controls(REAL_AXES)
    zero4 = scale(0, eye(4))
    need(
        all(anticommutator(a, b) == zero4 for a, b in combinations(REAL_AXES, 2)),
        "exact local anticommutation",
    )
    need(triple_product(REAL_AXES) == kron(I2, J), "real skew triple")
    ks, identity = joint_axes(REAL_AXES, REAL_AXES), eye(16)
    total, result = scale(0, identity), F(0)
    for signs in SIGNS:
        # Real Phi4 sources give unnormalized remote state E_b^T / 16.
        bob = scale(
            F(1, 4),
            multiply(
                add(identity, scale(signs[1], ks[1])),
                add(identity, scale(signs[2], ks[2])),
            ),
        )
        need(
            transpose(bob) == bob and multiply(bob, bob) == bob and trace(bob) == 4,
            "positive rank-four Bob outcome",
        )
        total = add(total, bob)
        robust_sos(ks, signs)
        for axis, k in enumerate(ks):
            mass = F(0)
            for a, c in product((-1, 1), repeat=2):
                pa = scale(F(1, 2), add(eye(4), scale(a, REAL_AXES[axis])))
                pc = scale(F(1, 2), add(eye(4), scale(c, REAL_AXES[axis])))
                probability = trace(multiply(kron(pa, pc), bob)) / 16
                need(probability >= 0, "positive real all-output probability")
                mass += probability
                result += signs[axis] * a * c * probability
            need(mass == F(1, 4), "no outcome selection")
        h = scale(0, identity)
        for sign, k in zip(signs, ks, strict=True):
            h = add(h, scale(sign, k))
        residual = add(
            add(scale(2, identity), scale(-1, triple_product(ks))), scale(-1, h)
        )
        # Its commuting spectrum lies in {0,4}; this polynomial plus symmetry
        # proves positivity exactly for this control, without float eigenvalues.
        need(
            transpose(residual) == residual
            and multiply(residual, residual) == scale(4, residual),
            "exact calibrated operator majorant",
        )
    need(total == identity and result == 2, "complete sharp real control")
    return result


def complex_native_control() -> F:
    for axis in AXES:
        choices = [u for u in cliffords() if turned(u, COMPLEX_Z) == axis]
        analyzer = min(
            choices, key=lambda u: tuple((z.re, z.im) for row in u for z in row)
        )
        need(
            run(gaussian_eye(2), synthesize(analyzer)) == analyzer,
            "two-logical-port native Pauli calibration",
        )
    result = F(0)
    for i, axis in enumerate(AXES):
        mass = F(0)
        for b1, b2, a, c in product((0, 1), (0, 1), (-1, 1), (-1, 1)):
            signs = (1 if b2 == 0 else -1, 1 if b1 == 0 else -1, -1 if b1 == b2 else 1)
            probability = network_probability(
                effect(axis, a), gram(bell_ket(b1, b2)), effect(axis, c)
            )
            mass += probability
            result += signs[i] * a * c * probability
        need(mass == 1, "all complex outcomes retained")
    need(result == 3, "complex Pauli source-parity score")
    return result


def boundary_cheats() -> None:
    left, right = (Z, Z, Z), (Z, Z, scale(-1, Z))
    ks = joint_axes(left, right)
    need(
        sum(s * k[0][0] for s, k in zip((1, 1, -1), ks, strict=True)) == 3,
        "commuting axes and product real sources cheat",
    )
    for axes in (left, right):
        reflection_controls(axes)
        need(
            multiply(symmetric(triple_product(axes)), symmetric(triple_product(axes)))
            == I2,
            "cheat triple norm is one, not zero",
        )

    # Bob's setting-dependent choice is a DIFFERENT instrument for each axis.
    ks = joint_axes(REAL_AXES, REAL_AXES)
    identity, leaked = eye(16), F(0)
    for i, k in enumerate(ks):
        for sign in (-1, 1):
            bob = scale(F(1, 2), add(identity, scale(sign, k)))
            need(
                multiply(bob, bob) == bob and trace(bob) == 8,
                "positive setting-leak measurement",
            )
            need(
                any(s[i] == sign for s in SIGNS),
                "valid odd-parity report for either branch",
            )
            leaked += sign * trace(multiply(k, bob)) / 16
    need(leaked == 3, "setting-dependent Bob defeats the calibrated separation")

    def direct_sum(a: Matrix, b: Matrix) -> Matrix:
        return tuple(row + (F(0),) * len(b) for row in a) + tuple(
            (F(0),) * len(a) + row for row in b
        )

    hidden = tuple(direct_sum(a, Z) for a in REAL_AXES)
    hidden_c = tuple(direct_sum(a, c) for a, c in zip(REAL_AXES, right, strict=True))
    for hidden_axes in (hidden, hidden_c):
        reflection_controls((hidden_axes[0], hidden_axes[1], hidden_axes[2]))
    p = multiply(multiply(hidden[0], hidden[1]), hidden[2])
    sym = symmetric(p)
    need(
        all(sym[i][j] == 0 for i in range(4) for j in range(6)),
        "tested block has zero symmetric triple",
    )
    need(sym[4][4] == 1, "untested occupied block invalidates global calibration")
    need(
        sum(
            sign * a[4][4] * c[4][4]
            for sign, a, c in zip((1, 1, -1), hidden, hidden_c, strict=True)
        )
        == 3,
        "untested real product support attains three despite good calibration block",
    )
    p = triple_product(REAL_AXES)
    good_loop, bad_loop = multiply(p, p), eye(4)
    need(
        good_loop == scale(-1, bad_loop),
        "skew and symmetric triples have opposite double-loop signs",
    )
    need(
        all(
            x * x == y * y
            for ar, br in zip(good_loop, bad_loop, strict=True)
            for x, y in zip(ar, br, strict=True)
        ),
        "phase-blind port returns do not identify that loop sign",
    )


def approximate_and_geometric_controls() -> None:
    perturbed: Triple = (
        REAL_AXES[0],
        REAL_AXES[1],
        add(scale(F(4, 5), REAL_AXES[2]), scale(F(3, 5), REAL_AXES[0])),
    )
    reflection_controls(perturbed)
    sym = symmetric(triple_product(perturbed))
    need(
        multiply(sym, sym) == scale(F(9, 25), eye(4)), "exact e=3/5 calibration control"
    )
    need(
        anticommutator(perturbed[0], perturbed[2]) == scale(F(6, 5), eye(4)),
        "pair norm bound attained",
    )
    ks = joint_axes(perturbed, perturbed)
    need(
        multiply(ks[0], ks[2]) != multiply(ks[2], ks[0]),
        "robust control does not assume commuting K",
    )
    for signs in SIGNS:
        robust_sos(ks, signs)

    for x, y in ((F(1), F(0)), (F(4, 5), F(3, 5)), (F(3, 5), F(4, 5))):
        plus: Matrix = ((x, y), (y, -x))
        minus: Matrix = ((x, -y), (-y, -x))
        us: Triple = (plus, minus, plus)
        reflection_controls(us)
        m, t = 3 * x, -triple_product(us)[0][0]
        need(
            F(3, 2) <= m <= 3 and t == m - 4 * m**3 / 27,
            "rational equal-angle geometric equality control",
        )
        # Supporting tangent, checked without introducing floating sqrt(3).
        need(2 * m + t >= 0 and (2 * m + t) ** 2 <= 27, "geometric tangent control")
        robust_sos((scale(-1, us[0]), us[1], us[2]), (-1, 1, 1))
    need(
        F(27, 4) < F(13, 5) ** 2 and F(13, 5) < F(8, 3),
        "one-skew-side rational improvement",
    )


def main() -> None:
    real, complex_value = real_sharp_control(), complex_native_control()
    boundary_cheats()
    approximate_and_geometric_controls()
    print(
        f"Three matched axes/all 48 cells: calibrated real bound {real} attained by positive independent Phi4 sources; supplied native complex Pauli network gives {complex_value}."
    )
    print(
        "Robust exact SOS: M<=8/3+e_A*e_C/3. Analytical geometry sharpens this to 3*cos(arccos(e_A*e_C)/3); one skew side gives 3*sqrt(3)/2<13/5."
    )
    print(
        "Commuting-axis and setting-leak cheats give 3; untested hidden support defeats local calibration. Bob-first/fresh-setting and phase-sensitive process calibration remain supplied."
    )
    print(
        "Conditional finite controls and analytical arguments only: no experimental significance, device-independent claim, new proof status, Born rule or QM derivation."
    )


if __name__ == "__main__":
    main()
