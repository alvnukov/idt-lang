"""Local charged-cone persistence for one supplied real, periodic junction walk.

SOURCE AND SCOPE. Use the exact representative in probe_routed_diamond_cones:
R_A rows=(1,2,3,0), R_B rows=(1,3,0,2), G=11^T/2-I and
F(kappa)=D C_B D* C_A, C_*=G R_*, D=diag(1,exp(i*kappa_j)).
At Q=(pi,0,0), F0 has eigenvalues exp(+/-i*pi/3), each twice. A real
translation-periodic local junction rule, the fixed two-sublattice cell,
lossless wave amplitudes, and the Bloch/Fourier description are supplied.
This is not a claim about arbitrary disorder, arbitrary discrete rewiring,
nonunitary loss, unsigned microscopic implementability, or particle species.

EXACT LOCAL ARGUMENT. K=2F0-I obeys K^2=-3I, K^T=-K, and the two spectral
clusters have chordal separation sqrt(3). Write P+=(I-iK/sqrt(3))/2.
Since partial_j F=i H_j F, H_j=E_j-V E_j V^T, their compressed, untilted
linear generators have Gram matrix
    g=[[2,-1,-1],[-1,2,0],[-1,0,2]]/12, det(g)=1/432.
For U=e^(+i theta) exp(+i h.sigma), the oriented phase-generator determinant
in the ORDERED kappa coordinates is -1/(12 sqrt(3)) in the plus cluster.
It is positive in the minus cluster. The smallest singular value is
sigma=sqrt((2-sqrt(2))/12)>0. Exact Clifford and trace checks are below.

Choose a smooth frame for the separated rank-two projector by projecting
a fixed frame and applying its positive Gram inverse square root. In that
frame remove the determinant phase from the 2x2 unitary. Its traceless
Hermitian sine part is h(kappa,eta). Near the identity, h=0 is exactly a
double eigenvalue, not merely a small eigenvalue gap. This map is analytic
and its kappa Jacobian has the nonzero determinant above. The implicit
function theorem therefore gives a UNIQUE nearby simple Weyl point per
cluster for every sufficiently small smooth unitary junction perturbation.
Reality is not needed for this existence argument; it pairs the two points.
Thus these crossings are not protected ONLY by the high-symmetry corner.

FLUX ARGUMENT. At eta=0, h(q)=Jq+O(|q|^2). On a sufficiently small sphere,
the straight homotopy from h to Jq never vanishes, so its normalized degree
is sign(det J). The two eigenlines have opposite UNIT Chern numbers.
A useful quantitative sufficient condition is
    sup_boundary |h_eta(q)-Jq| < sigma*r.
It preserves the degree. If additionally sup_ball ||Dh_eta-J|| < sigma,
the map is injective and the enclosed zero is unique and regular. Smoothness
supplies these inequalities for sufficiently small r and eta. No explicit
universal numerical radius or mesh-certified remainder bound is claimed.
External cluster isolation has the elementary sufficient bound
    2*||q||_infinity + ||delta C_A|| + ||delta C_B|| < sqrt(3)/4,
because ||F(Q+q,eta)-F0|| is at most the left side. This isolation bound
alone is NOT an internal Weyl-gap or uniqueness bound.

CONCRETE REAL LOCAL DEFORMATION. At junction A only, set
n(e)=cos(e)*(1,1,1,1)/2 + sin(e)*(1,-1,1,-1)/2,
G_A(e)=2 n(e)n(e)^T-I, C_A(e)=G_A(e)R_A. This is real orthogonal, with
positive n entries for |e|<pi/4; the wiring and unit cell do not change.
The factor ordering is explicit: G commutes with R_A at the base but G_A(e)
need not. Here R_A n=n and R_A t=-t, so using R_A G_A(e) instead is exactly
the written family with e replaced by -e; the displacement signs reverse.
Exact compressed perturbation traces give
    kappa_+'(0)=(0,sqrt(3),sqrt(3)), theta_+'(0)=1/sqrt(3).
The conjugate point moves oppositely and has opposite carrier phase.
Here ||G_A(e)-G||=2|sin(e)|. Hence |e|<=1/100 and |q|<=2/25 obey
the external-cluster bound by 2*(2/25)+2/100=9/50<sqrt(3)/4.
This exact outer-gap estimate still does not certify the internal mesh gaps.
These continuous junction angles are a supplied perturbation resource,
not compiled from the original fixed junction by this probe.

SIGN CONVENTIONS MATTER. Here Berry A=-i<u|du>, outward kappa-oriented
spheres, and bands are ordered by increasing principal EIGENPHASE. Then
the upper relative-phase line has charge sign(det J). At Q the four charges
are (-1,+1,+1,-1). Using Berry A=+i<u|du> reverses every charge. Defining
quasienergy by U=exp(-i*epsilon) reverses the phase-generator orientation
and swaps upper/lower labels. The tetrahedral spatial chart has det(JAC)=-16,
so switching from kappa to its ordered physical coordinates also reverses
the stated orientation. None is a count of Standard Model species.

For REAL junctions F(-k)=conj(F(k)). Around conjugate points,
h_-(q)=-conj(h_+(-q)); at linear order H_j^- = conj(H_j^+). Conjugation
reflects the Pauli y coordinate, giving OPPOSITE phase-cone determinants.
But conjugation of a line bundle and inversion of its enclosing sphere each
reverse Chern sign: the CONJUGATE-RELATED INDIVIDUAL BANDS have the SAME
charge, with upper plus-phase paired to lower minus-phase. This differs
from the usual static-Hamiltonian time-reversal chirality shortcut.

OPTIONAL NUMERICAL AUDIT. --numeric uses installed NumPy, no optimizer or
new package installation. A local Newton solve in the canonical projector
frame checks e=+/-0.01. Gauge-invariant triangular overlap fluxes are checked
for ALL FOUR bands on two octahedral refinements, around each moved point
and around both together. Sampled gaps, link overlaps and residuals are
reported; these are finite floating-point controls, not interval-certified
topology or an experimental fit. The local mathematical argument above is
separate, and is not a Lean proof. No continuous Brillouin-zone exhaustion,
absence of other valleys, or global band-by-band charge census is asserted.

Run: python3 -B -O -m scripts.probe_collision_cone_stability [--numeric]
"""

from __future__ import annotations

import argparse
import sys
from dataclasses import dataclass
from fractions import Fraction as F
from itertools import product
from pathlib import Path
from typing import TYPE_CHECKING, cast

if TYPE_CHECKING:
    import numpy as np
    from numpy.typing import NDArray

    FloatArray = NDArray[np.float64]
    ComplexArray = NDArray[np.complex128]

if not __package__:
    sys.path.insert(0, str(Path(__file__).resolve().parents[1]))

from scripts.probe_balanced_phase_composition import (
    Matrix,
    add,
    determinant,
    matrix,
    multiply,
    scale,
    trace,
    transpose,
)
from scripts.probe_routed_diamond_cones import (
    I4,
    JAC,
    G,
    conjugate,
    derivatives,
    diag,
    sub,
)


def need(ok: bool, reason: str) -> None:
    if not ok:
        raise ArithmeticError(reason)


RA = tuple(I4[j] for j in (1, 2, 3, 0))
RB = tuple(I4[j] for j in (1, 3, 0, 2))
N = (F(1, 2),) * 4
T = (F(1, 2), F(-1, 2), F(1, 2), F(-1, 2))


def outer(a: tuple[F, ...], b: tuple[F, ...]) -> Matrix:
    return matrix(tuple(tuple(x * y for y in b) for x in a))


def exact_controls() -> None:
    ca, cb = multiply(G, RA), multiply(G, RB)
    v = conjugate(diag((1, -1, 1, 1)), cb)
    f0 = multiply(v, ca)
    k = sub(scale(2, f0), I4)
    need(multiply(k, k) == scale(-3, I4), "carrier polynomial")
    need(transpose(k) == scale(-1, k), "carrier complex structure")
    linear = tuple(
        scale(F(1, 2), sub(h, scale(F(1, 3), multiply(multiply(k, h), k))))
        for h in derivatives(v)
    )
    need(all(trace(h) == 0 for h in linear), "first-order phase tilt")
    gram = matrix(
        tuple(tuple(trace(multiply(a, b)) / 4 for b in linear) for a in linear)
    )
    expected = scale(F(1, 12), matrix(((2, -1, -1), (-1, 2, 0), (-1, 0, 2))))
    need(gram == expected and determinant(gram) == F(1, 432), "full-rank metric")
    for j, l in product(range(3), repeat=2):
        need(
            add(multiply(linear[j], linear[l]), multiply(linear[l], linear[j]))
            == scale(2 * gram[j][l], I4),
            "Clifford metric",
        )
    need(
        all(multiply(k, h) == multiply(h, k) for h in linear),
        "spectral-block compression",
    )
    comm = sub(multiply(linear[1], linear[2]), multiply(linear[2], linear[1]))
    signed_trace = trace(multiply(k, multiply(linear[0], comm)))
    need(signed_trace == F(2, 3), "plus-cluster determinant sign")
    # det(J_+)=-signed_trace/(8 sqrt(3)); this fixes the branch convention.
    need(signed_trace**2 / 192 == determinant(gram), "oriented volume magnitude")
    need(determinant(JAC) == -16, "spatial-coordinate orientation")
    spatial = multiply(multiply(transpose(JAC), gram), JAC)
    need(
        spatial == scale(F(1, 3), matrix(((4, 0, 0), (0, 2, 0), (0, 0, 2)))),
        "spatial metric",
    )
    # Characteristic polynomial of 12*g: (x-2)*((x-2)^2-2).
    centered = sub(scale(12, gram), matrix(((2, 0, 0), (0, 2, 0), (0, 0, 2))))
    need(
        multiply(multiply(centered, centered), centered) == scale(2, centered),
        "singular-value certificate",
    )
    need(sum(x * x for x in N) == sum(x * x for x in T) == 1, "junction directions")
    need(sum(x * y for x, y in zip(N, T, strict=True)) == 0, "junction tangent")
    need(sub(scale(2, outer(N, N)), I4) == G, "base junction")
    derivative_g = scale(2, add(outer(T, N), outer(N, T)))
    need(conjugate(RA, G) == G, "base routing commutation")
    need(
        conjugate(RA, derivative_g) == scale(-1, derivative_g),
        "deformed routing order reverses this angle",
    )
    angle_generator = multiply(derivative_g, G)
    need(
        angle_generator == scale(2, sub(outer(T, N), outer(N, T))),
        "real junction derivative",
    )
    need(
        transpose(angle_generator) == scale(-1, angle_generator),
        "orthogonal perturbation tangent",
    )
    s = conjugate(v, angle_generator)
    tilt_numerator = -trace(multiply(k, s)) / 4
    pairings = tuple(-trace(multiply(k, multiply(h, s))) / 4 for h in linear)
    need(
        tilt_numerator == 1 and pairings == (F(1, 2), F(-1, 2), F(-1, 2)),
        "compressed angle perturbation",
    )
    shift_numerators = (F(0), F(3), F(3))
    need(
        all(
            sum(gram[j][l] * shift_numerators[l] for l in range(3)) + pairings[j] == 0
            for j in range(3)
        ),
        "implicit cone displacement",
    )
    # Pauli conjugation is reflection in y. Momentum inversion and the
    # phase sign cancel in h_-(q)=-conj(h_+(-q)), leaving that reflection.
    pauli_conjugation = matrix(((1, 0, 0), (0, -1, 0), (0, 0, 1)))
    need(determinant(pauli_conjugation) == -1, "conjugate cone orientation")
    need(determinant(scale(-1, pauli_conjugation)) == 1, "static-TR contrast")
    # Norm bound 2*r+deltaA+deltaB<sqrt(3)/4 isolates clusters only.
    external_bound = 2 * F(2, 25) + 2 * F(1, 100)
    need(external_bound == F(9, 50), "chosen external-gap window")
    need(external_bound**2 < F(3, 16), "explicit external-gap neighborhood")


@dataclass(frozen=True)
class Flux:
    charges: tuple[float, float, float, float]
    sampled_gap: float
    minimum_link: float
    vertices: int


def numerical_controls() -> None:
    """Optional finite floating-point audit, deliberately separate from exact checks."""
    import numpy as np

    def real_array(values: object) -> FloatArray:
        return np.asarray(values, dtype=np.float64)

    def complex_array(values: object) -> ComplexArray:
        return np.asarray(values, dtype=np.complex128)

    g0 = real_array([[float(x) for x in row] for row in G])
    ra = real_array([[float(x) for x in row] for row in RA])
    rb = real_array([[float(x) for x in row] for row in RB])
    n, t = real_array([float(x) for x in N]), real_array([float(x) for x in T])
    cb = g0 @ rb
    center = real_array([np.pi, 0.0, 0.0])

    def flow(momentum: FloatArray, angle: float) -> ComplexArray:
        direction = np.cos(angle) * n + np.sin(angle) * t
        need(
            bool(np.all(direction > 0)),
            "test junction left positive-weight neighborhood",
        )
        ca = (2 * np.outer(direction, direction) - np.eye(4)) @ ra
        d = np.diag(np.exp(1j * np.concatenate(([0.0], momentum))))
        out = complex_array(d @ cb @ d.conj().T @ ca)
        need(
            float(np.linalg.norm(out.conj().T @ out - np.eye(4))) < 1e-12,
            "numerical unitarity",
        )
        return out

    f0 = flow(center, 0.0)
    _, carrier_frames = np.linalg.eigh(-1j * (2 * f0 - np.eye(4)))
    reference = {
        1: complex_array(carrier_frames[:, 2:]),
        -1: complex_array(carrier_frames[:, :2]),
    }

    def effective(
        momentum: FloatArray, angle: float, branch: int = 1
    ) -> tuple[FloatArray, float]:
        u = flow(momentum, angle)
        values, eigenvectors = np.linalg.eig(u)
        distances = np.abs(values - np.exp(1j * branch * np.pi / 3))
        order = np.argsort(distances)
        need(
            float(distances[order[2]] - distances[order[1]]) > 0.5,
            "ambiguous spectral cluster",
        )
        q = np.linalg.qr(eigenvectors[:, order[:2]])[0]
        projector = q @ q.conj().T
        w0 = reference[branch]
        metric = w0.conj().T @ projector @ w0
        norms, frame = np.linalg.eigh(metric)
        need(float(np.min(norms)) > 0.8, "canonical frame lost its chart")
        w = projector @ w0 @ frame @ np.diag(1 / np.sqrt(norms)) @ frame.conj().T
        block = w.conj().T @ u @ w
        phase = float(np.angle(np.linalg.det(block))) / 2
        special = np.exp(-1j * phase) * block
        hermitian = (special - special.conj().T) / (2j)
        need(abs(complex(np.trace(hermitian))) < 1e-10, "nontraceless SU2 sine")
        h = real_array(
            [
                hermitian[0, 1].real,
                -hermitian[0, 1].imag,
                (hermitian[0, 0].real - hermitian[1, 1].real) / 2,
            ]
        )
        return h, phase

    def jacobian(momentum: FloatArray, angle: float, branch: int = 1) -> FloatArray:
        step = 2e-5
        axes = np.eye(3) * step
        return real_array(
            np.column_stack(
                [
                    (
                        effective(momentum + axis, angle, branch)[0]
                        - effective(momentum - axis, angle, branch)[0]
                    )
                    / (2 * step)
                    for axis in axes
                ]
            )
        )

    def locate(angle: float) -> tuple[FloatArray, float, float]:
        momentum = center + real_array([0.0, np.sqrt(3) * angle, np.sqrt(3) * angle])
        for _ in range(12):
            h, phase = effective(momentum, angle)
            residual = float(np.linalg.norm(h))
            if residual < 1e-12:
                return momentum, phase, residual
            momentum = real_array(
                momentum - np.linalg.solve(jacobian(momentum, angle), h)
            )
        raise ArithmeticError("bounded local Newton audit did not converge")

    def mesh(level: int) -> tuple[list[FloatArray], list[tuple[int, int, int]]]:
        vertices = [
            real_array(v)
            for v in (
                (1, 0, 0),
                (-1, 0, 0),
                (0, 1, 0),
                (0, -1, 0),
                (0, 0, 1),
                (0, 0, -1),
            )
        ]
        faces: list[tuple[int, int, int]] = []
        for a, b, c in product(range(2), repeat=3):
            face = (a, 2 + b, 4 + c)
            if float(np.linalg.det(np.stack([vertices[j] for j in face]))) < 0:
                face = face[0], face[2], face[1]
            faces.append(face)
        for _ in range(level):
            edges: dict[tuple[int, int], int] = {}
            refined: list[tuple[int, int, int]] = []

            def midpoint(i: int, j: int, edge_cache: dict[tuple[int, int], int]) -> int:
                edge = min(i, j), max(i, j)
                if edge not in edge_cache:
                    vector = vertices[i] + vertices[j]
                    edge_cache[edge] = len(vertices)
                    vertices.append(real_array(vector / np.linalg.norm(vector)))
                return edge_cache[edge]

            for a, b, c in faces:
                ab, bc, ca = (
                    midpoint(a, b, edges),
                    midpoint(b, c, edges),
                    midpoint(c, a, edges),
                )
                refined.extend(((a, ab, ca), (ab, b, bc), (ca, bc, c), (ab, bc, ca)))
            faces = refined
        need(
            len(vertices) - 3 * len(faces) // 2 + len(faces) == 2,
            "sphere mesh Euler check",
        )
        oriented_edges: dict[tuple[int, int], int] = {}
        for a, b, c in faces:
            need(
                float(np.linalg.det(np.stack([vertices[j] for j in (a, b, c)]))) > 0,
                "inward sphere triangle",
            )
            for i, j in ((a, b), (b, c), (c, a)):
                oriented_edges[i, j] = oriented_edges.get((i, j), 0) + 1
        need(
            all(
                count == 1 and oriented_edges.get((j, i)) == 1
                for (i, j), count in oriented_edges.items()
            ),
            "open or duplicated mesh edge",
        )
        return vertices, faces

    def flux(origin: FloatArray, angle: float, radius: float, level: int) -> Flux:
        vertices, faces = mesh(level)
        states: list[ComplexArray] = []
        sampled_gap, minimum_link = 10.0, 1.0
        for vertex in vertices:
            values, vectors = np.linalg.eig(flow(origin + radius * vertex, angle))
            order = np.argsort(np.angle(values))
            values, vectors = values[order], vectors[:, order]
            vectors = vectors / np.linalg.norm(vectors, axis=0)
            states.append(complex_array(vectors))
            sampled_gap = min(
                sampled_gap,
                min(
                    float(abs(values[j] - values[k]))
                    for j in range(4)
                    for k in range(j)
                ),
            )
        charges = np.zeros(4)
        for a, b, c in faces:
            ab = np.sum(states[a].conj() * states[b], axis=0)
            bc = np.sum(states[b].conj() * states[c], axis=0)
            ca = np.sum(states[c].conj() * states[a], axis=0)
            minimum_link = min(
                minimum_link,
                float(np.min(abs(ab))),
                float(np.min(abs(bc))),
                float(np.min(abs(ca))),
            )
            # Arg(overlap product) corresponds to A=-i<u|du>.
            charges += np.angle(ab * bc * ca)
        charges /= 2 * np.pi
        return Flux(
            (
                float(charges[0]),
                float(charges[1]),
                float(charges[2]),
                float(charges[3]),
            ),
            sampled_gap,
            minimum_link,
            len(vertices),
        )

    def check_sphere(
        label: str,
        origin: FloatArray,
        angle: float,
        radius: float,
        expected: tuple[int, int, int, int],
    ) -> None:
        previous: Flux | None = None
        for level in (2, 3):
            result = flux(origin, angle, radius, level)
            need(
                max(
                    abs(x - target)
                    for x, target in zip(result.charges, expected, strict=True)
                )
                < 1e-8,
                "all-band flux: " + label,
            )
            need(abs(sum(result.charges)) < 1e-8, "complete four-band bundle")
            need(
                result.sampled_gap > 0.001 and result.minimum_link > 0.6,
                "poorly resolved sampled sphere",
            )
            if previous is not None:
                need(
                    max(
                        abs(x - y)
                        for x, y in zip(result.charges, previous.charges, strict=True)
                    )
                    < 1e-8,
                    "mesh-refinement flux mismatch",
                )
            previous = result
        result = cast(Flux, previous)
        print(
            f"  {label}: C={expected}, sampled chord gap={result.sampled_gap:.6g}, min link={result.minimum_link:.6g}, vertices={result.vertices}."
        )

    plus_jac = jacobian(center, 0.0)
    minus_jac = jacobian(center, 0.0, -1)
    need(
        abs(float(np.linalg.det(plus_jac)) + 1 / (12 * np.sqrt(3))) < 1e-8,
        "numerical plus orientation",
    )
    need(
        abs(float(np.linalg.det(minus_jac)) - 1 / (12 * np.sqrt(3))) < 1e-8,
        "numerical minus orientation",
    )
    check_sphere("unperturbed", center, 0.0, 0.08, (-1, 1, 1, -1))
    for angle in (0.01, -0.01):
        point, phase, residual = locate(angle)
        partner = real_array(2 * center - point)
        need(
            float(np.linalg.norm(flow(partner, angle) - flow(point, angle).conj()))
            < 1e-12,
            "real-walk conjugation",
        )
        need(
            float(np.linalg.det(jacobian(point, angle))) < 0
            and float(np.linalg.det(jacobian(partner, angle, -1))) > 0,
            "moved chirality",
        )
        shift = point - center
        need(
            float(
                np.linalg.norm(
                    shift - real_array([0.0, np.sqrt(3) * angle, np.sqrt(3) * angle])
                )
            )
            < 2 * angle**2,
            "first-order displacement audit",
        )
        need(
            abs(phase - np.pi / 3 - angle / np.sqrt(3)) < angle**2,
            "carrier phase derivative audit",
        )
        print(
            f"angle={angle:+.3f}: kappa shift={tuple(float(x) for x in shift)}, phase={phase:.12f}, residual={residual:.3g}."
        )
        check_sphere("plus carrier", point, angle, 0.01, (0, 0, 1, -1))
        check_sphere("minus carrier", partner, angle, 0.01, (-1, 1, 0, 0))
        check_sphere("enclosing both", center, angle, 0.08, (-1, 1, 1, -1))


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--numeric",
        action="store_true",
        help="optional existing-NumPy all-band flux audit",
    )
    args = parser.parse_args()
    exact_controls()
    print(
        "Exact representative: det Gram=1/432; phase-cone determinants in kappa coordinates are -/+1/(12 sqrt(3))."
    )
    print(
        "Local analytic IFT and degree argument give persistent unit-charge cones for sufficiently small periodic unitary junction changes."
    )
    print(
        "Real positive-weight A-junction deformation: kappa_+'=(0,sqrt(3),sqrt(3)), theta_+'=1/sqrt(3)."
    )
    print(
        "Conjugate phase cones have opposite handedness; conjugate-related individual bands have equal Berry charge after label exchange."
    )
    if args.numeric:
        numerical_controls()
    print(
        "No certified numerical persistence radius, global valley census, disorder theorem, or particle-species identification."
    )


if __name__ == "__main__":
    main()
