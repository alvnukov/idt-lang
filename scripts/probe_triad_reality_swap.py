"""A prospective conjugate-analyzer test; not a device-independent reality test.

The null supplies three independent (possibly mixed) internal states that
are all real in one common representation, passive internal-blind spatial
optics with two truly conjugate transfer matrices, ordinary bosonic exchange
and the same number-resolving instrument in both settings. For any number
of real internal dimensions, all permutation-cycle traces are real; complex
conjugation of the spatial kernel leaves every output probability unchanged.
No author dataset for this new two-setting protocol is assumed to exist.
"""

from __future__ import annotations

from fractions import Fraction as F
from itertools import permutations

from scripts import probe_packet_triad_phase as tri
from scripts.gaussian_dyadic_words import ONE, ZERO, Gaussian, Matrix, eye, g, run
from scripts.probe_native_rational_pentagon import add, multiply, scale


def trace(m: Matrix) -> Gaussian:
    return sum((r[i] for i, r in enumerate(m)), ZERO)


def density(v: tuple[Gaussian, ...]) -> Matrix:
    return tuple(tuple(x * y.star() for y in v) for x in v)


def cycles(rs: tuple[Matrix, ...]) -> tri.Kernel:
    out = {}
    for p in permutations(range(len(rs))):
        consumed = set()
        z = ONE
        for i in range(len(p)):
            if i in consumed:
                continue
            cur = i
            a = eye(len(rs[0]))
            while cur not in consumed:
                consumed.add(cur)
                a = multiply(a, rs[cur])
                cur = p[cur]
            z = z * trace(a)
        out[p] = z
    return out


def reference_controls() -> None:
    v = tri.states(ONE)
    a, b, rplus = tuple(density(x) for x in v)
    rminus = density(tri.states(g(-1))[2])
    u = run(eye(3), tri.THREE)
    conjugate = tuple(tuple(x.star() for x in row) for row in u)
    need = tri.need
    need(
        run(eye(3), tuple(op for op in tri.THREE for _ in range(3))) == conjugate,
        "wrong conjugate native circuit",
    )
    for t in (F(0), F(1, 5), F(1, 2), F(3, 4), F(1)):
        mixed = add(scale(rplus, g(t)), scale(rminus, g(1 - t)))
        weights = cycles((a, b, mixed))
        need(all(z.im == 0 for z in weights.values()), "counterfeit not a real source")
        need(weights[tri.CYCLE] == g((2 * t - 1) / 8), "wrong real triple")
        need(trace(multiply(mixed, mixed)) == g(t * t + (1 - t) ** 2), "mixture purity")
        for i, j in ((a, b), (a, mixed), (b, mixed)):
            need(
                trace(multiply(i, j)) == g(F(1, 4)),
                "pairwise distinguishability changed",
            )
        for o in tri.occupations(3, 3):
            need(
                tri.probability(tri.spatial_kernel(u, o), weights)
                == tri.probability(tri.spatial_kernel(conjugate, o), weights),
                "real mixed orientation bias",
            )
        # This reproduces the EVEN ideal-tritter cosine benchmark without
        # any continuously changing pure real triad phase; NOT the measured
        # apparatus/purity. It cannot mimic the analyzer-odd discriminator.
        ideal = (2 - F(3, 4) + 4 * weights[tri.CYCLE].re) / 9
        need(ideal == F(1, 12) + t * F(1, 9), "real cosine counterfeit")


def max_purity(cyclic: F) -> F:
    # Two trusted real pure references have overlap +1/2. For a third real
    # density, equal overlap probabilities 1/4 fix the diagonal quadratic
    # forms. Its restriction to their span has these two eigenvalues in the
    # normalized sum/difference basis. Interlacing bounds its second eigenvalue.
    # Imaginary cross terms would invalidate this restriction argument.
    if abs(cyclic) > F(1, 8):
        raise ValueError("not feasible at these fixed pair magnitudes")
    mu = min(F(1, 6) + F(4, 3) * cyclic, F(1, 2) - 4 * cyclic)
    return (1 - mu) ** 2 + mu**2


def orientation_control() -> None:
    u = run(eye(3), tri.THREE)
    v = tuple(tuple(z.star() for z in row) for row in u)
    cells = tri.occupations(3, 3)
    all_coeff = {}
    for o in cells:
        k = tri.spatial_kernel(u, o)[tri.CYCLE]
        all_coeff[o] = -4 * k.im
    need = tri.need
    need(
        all_coeff[(2, 1, 0)] == F(1, 4) and sum(all_coeff.values()) == 0,
        "orientation coefficient",
    )
    for s in tri.UNITS:
        internal = tri.states(s)
        weights = cycles(tuple(density(x) for x in internal))
        need(
            weights == tri.overlap_cycles(tri.gram(internal)),
            "mixed-state formula different on pure sources",
        )
        pu, pv = tri.distribution(u, internal), tri.distribution(v, internal)
        for o in cells:
            need(
                pu[o] - pv[o] == all_coeff[o] * weights[tri.CYCLE].im,
                "orientation-only contrast",
            )
    need(
        max_purity(F(0)) == F(13, 18)
        and max_purity(F(1, 8)) == 1
        and max_purity(F(-1, 8)) == 1,
        "purity boundary",
    )
    print(
        f"One preregisterable occupation (2,1,0): P(U)-P(conjugate U)=Im Tr(rho1 rho2 rho3)/4, ideal signal -1/32 for s=i. All-output absolute coefficient sum {sum(abs(x) for x in all_coeff.values())}."
    )


def main() -> None:
    reference_controls()
    orientation_control()
    print(
        "Every common-real independent mixed-state model gives zero difference under the calibrated internal-blind conjugate-analyzer contract. A real mixed third state fakes the EVEN scalar fringe with unchanged pair overlaps. With two calibrated pure real references, zero triple trace bounds the third purity by 13/18."
    )
    print(
        "This is not a retrospective test of Menssen data, or an exclusion of real QM, correlated emissions, internal-resolving apparatus, settings-dependent losses, or models with a shared auxiliary phase. The photon exchange and measurement laws are supplied."
    )


if __name__ == "__main__":
    main()
