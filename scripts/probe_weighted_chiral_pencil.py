"""No-rank-10 reconstruction with arbitrary NONZERO complex entry weights.

Fix the ten symmetric five-slot pair supports, not an exchange law or metric.
Relative to the exterior witness let t_e be the ratio at undirected edge e.
On each of 80 hexagons the alternating matching ratio must be 1 for t: the
reference already supplies the cancelling sign. Otherwise the three-axis
sum at unit coefficients has rank 10 (two stars of rank 2 and a hexagon of
rank 6). Nonzero entries are needed for that argument. The full pencil is
over complex freely selectable coefficients; lack of rank 10 is a selection
hypothesis, not an observation. See probe_chiral_pencil_signs for the support
and the reference's exact all-coefficient rank argument.

C has alternating integer hexagon rows; G has unsigned state/channel
redefinition rows. C G^T=0. Let J,K partition the edges as below. Both
C[I,J] and M=G[P,K] have determinant +/-1 OVER THE INTEGERS. On the 20
independent complex edge ratios z=t_K, assign the 20 gauge factors
    alpha_p = product_j z_j ** (M^-1)[j,p] .
Multiplying the reference by these gauges recovers t on K. The residue is
1 on K and has unit cycle products, so C[I,J]^-1 makes it 1 on J too.
All powers are integral: no branch of logarithm, root choices, torsion
exceptions or generic-weight approximation. The actual exponent matrices
are returned by certificate(). Thus no rank 10 iff in the reference orbit
under invertible DIAGONAL matter AND channel scalings. General GL is not
needed; neither physical scale equivalence nor unitary equivalence follows.

With only phases disposable, the 20 magnitudes |z_j| are independent and
complete calibrated coordinates, not 20 predictions. Quotient by arbitrary
positive gains of the ten channels leaves 10 magnitude dimensions. Fixing
each channel's Frobenius norm picks one representative of each gain orbit;
requiring equal norms without specifying their common value adds one common
scale. Requiring all individual edge magnitudes equal is much stronger:
only one common scale remains (none if calibrated). We do not infer equal
edge weights, masses, CKM, spin or a primitive physical rank protocol.

Run: python3 -B -O -m scripts.probe_weighted_chiral_pencil
"""

from __future__ import annotations

from dataclasses import dataclass
from fractions import Fraction as F
from math import lcm, prod

from scripts.probe_chiral_pencil_signs import (
    AXES,
    EDGES,
    EVEN,
    car_certificate,
    exterior_witness,
    need,
    rank_q,
    triple_checks,
)

Matrix = list[list[int]]
WE = tuple(sorted(EDGES, key=lambda e: e[:2]))
POS = {e[:2]: i for i, e in enumerate(WE)}
# Independently verifiable zero-based certificates. WE is sorted by its two
# vertex masks; AXES sorts by (slot,common occupation), creation having bit 0.
C_ROWS = (*range(17), 24, 25, 26)
J = (20, 3, 11, 12, 10, 21, 7, 25, 9, 17, 1, 30, 16, 4, 15, 26, 18, 8, 22, 13)
G_ROWS = (*range(15), 16, 17, 18, 20, 22)
K = tuple(i for i in range(40) if i not in J)


def tr(m: Matrix) -> Matrix:
    return [list(r) for r in zip(*m, strict=True)]


def matmul(a: Matrix, b: Matrix) -> Matrix:
    cols = tr(b)
    return [
        [sum(x * y for x, y in zip(row, col, strict=True)) for col in cols] for row in a
    ]


def eye(n: int) -> Matrix:
    return [[int(i == j) for j in range(n)] for i in range(n)]


def minor(a: Matrix, rows: tuple[int, ...], cols: tuple[int, ...]) -> Matrix:
    return [[a[r][j] for j in cols] for r in rows]


def inverse_integer(a: Matrix) -> tuple[int, Matrix]:
    n = len(a)
    aug = [[F(x) for x in row + unit] for row, unit in zip(a, eye(n), strict=True)]
    det = F(1)
    for j in range(n):
        p = next(r for r in range(j, n) if aug[r][j])
        if p != j:
            aug[p], aug[j] = aug[j], aug[p]
            det = -det
        v = aug[j][j]
        det *= v
        aug[j] = [x / v for x in aug[j]]
        for r in range(n):
            if r != j and (w := aug[r][j]):
                aug[r] = [y - w * x for x, y in zip(aug[j], aug[r], strict=True)]
    need(
        abs(det) == 1 and all(x.denominator == 1 for row in aug for x in row),
        "integral inverse",
    )
    inv = [[int(x) for x in row[n:]] for row in aug]
    need(matmul(a, inv) == matmul(inv, a) == eye(n), "two-sided integer certificate")
    return int(det), inv


def lattices() -> tuple[Matrix, Matrix]:
    cycles = []
    for mask in triple_checks().values():
        edges = [(a, b) for e, (a, b, _) in enumerate(EDGES) if mask >> e & 1]
        start = min(v for p in edges for v in p)
        prev = x = start
        row = [0] * 40
        for n in range(6):
            y = min(v for p in edges if x in p for v in p if v not in (x, prev))
            row[POS[min(x, y), max(x, y)]] = 1 - 2 * (n % 2)
            prev, x = x, y
        need(x == start and row.count(1) == row.count(-1) == 3, "oriented hexagon")
        cycles.append(row)
    g = [[int(m in (a, b)) for a, b, _ in WE] for m in EVEN] + [
        [int(k == l) for _, _, l in WE] for k in AXES
    ]
    need(
        matmul(cycles, tr(g)) == [[0] * 26 for _ in range(80)],
        "integer cycle cancellation",
    )
    return cycles, g


@dataclass
class Certificate:
    cycles: Matrix
    gauge: Matrix
    # rows of factors: Laurent exponents on the independent t_K for alpha_p
    factors: Matrix
    # rows of lift: same powers for ALL forty relative edge weights
    lift: Matrix
    # rows of undo_cycles: reconstruct residuals on J from cycle products I
    undo_cycles: Matrix


def certificate() -> Certificate:
    c, g = lattices()
    dc, undo = inverse_integer(minor(c, C_ROWS, J))
    dg, inv = inverse_integer(minor(g, G_ROWS, K))
    need((dc, dg) == (-1, 1), "signed integer witness determinants")
    chosen = [g[p] for p in G_ROWS]
    lift = tr(matmul(inv, chosen))
    need([lift[j] for j in K] == eye(20), "independent edge coordinates")
    need(matmul(c, lift) == [[0] * 20 for _ in c], "all cycle products identically one")
    # Full normalization identity for every t (even those failing constraints):
    # let E = I - lift * project_K. Then E t are log-free monomial exponents
    # of the residual t / reconstructed(t_K). On J, E_J = C[I,J]^-1 C[I,:].
    project = [eye(40)[j] for j in K]
    encoded = matmul(lift, project)
    residual = [
        [int(i == j) - v for j, v in enumerate(row)] for i, row in enumerate(encoded)
    ]
    need(
        [residual[j] for j in J] == matmul(undo, [c[i] for i in C_ROWS]),
        "universal Laurent normalization identity",
    )
    need(all(not any(residual[j]) for j in K), "anchor residuals")
    return Certificate(c, g, tr(inv), lift, undo)


def powers(rows: Matrix, values: list[F]) -> list[F]:
    """Demonstrate the same Laurent prescription in an exact number domain."""
    if not all(values):
        raise ValueError("normalization requires nonzero weights")
    return [
        prod((v**n for v, n in zip(values, row, strict=True) if n), start=F(1))
        for row in rows
    ]


def check_normalizer(c: Certificate) -> None:
    signs = exterior_witness()
    lookup = {e: (1 - 2 * (signs >> j & 1)) for j, e in enumerate(EDGES)}
    need(
        powers(c.cycles, [F(lookup[e]) for e in WE]) == [-1] * 80,
        "reference matching cancellation",
    )
    z = [F(1 - j if j > 1 else j + 1, j + 2) for j in range(20)]
    t = powers(c.lift, z)
    alpha = powers(c.factors, z)
    need(t == powers(tr([c.gauge[p] for p in G_ROWS]), alpha), "construct factors")
    need(
        [t[j] for j in K] == z and powers(c.cycles, t) == [1] * 80,
        "nonuniform surviving sample",
    )
    t[J[0]] *= 2
    res = powers(c.cycles, t)
    need(any(v != 1 for v in res), "corrupted nonzero edge caught by rank-ten triple")
    decoded = powers(c.undo_cycles, [res[i] for i in C_ROWS])
    need(decoded == [2] + [1] * 19, "explicitly decode known discrepancy")
    # An actual unequal-weight rank witness over Q, independently of the
    # integer-lattice calculation. Clear one common denominator, not rows.
    h = next(j for j, v in enumerate(res) if v != 1)
    axes = {e[2] for e, v in zip(WE, c.cycles[h], strict=True) if v}
    vals = [v * lookup[e] if e[2] in axes else F(0) for v, e in zip(t, WE, strict=True)]
    denominator = lcm(*(v.denominator for v in vals))
    matrix = [[0] * 16 for _ in EVEN]
    for (a, b, _), v in zip(WE, vals, strict=True):
        s = denominator * v
        need(s.denominator == 1, "cleared rank matrix")
        matrix[EVEN.index(a)][EVEN.index(b)] = matrix[EVEN.index(b)][EVEN.index(a)] = (
            int(s)
        )
    need(rank_q(matrix) == 10, "direct rational weighted rank-ten counterexample")
    # Roots-of-unity check without floating point: these integers encode
    # exponents of a primitive 12th root. The universal certificate above
    # uses no finite-order assumption.
    zph = [[j % 12] for j in range(20)]
    eph = matmul(c.lift, zph)
    aph = matmul(c.factors, zph)
    need(
        matmul(tr([c.gauge[p] for p in G_ROWS]), aph) == eph
        and all(v[0] % 12 == 0 for v in matmul(c.cycles, eph))
        and eph[K[1]][0] % 12 == 1,
        "complex phases with a nonreal component",
    )
    car_certificate()


def metric_controls(c: Certificate) -> None:
    # Per-channel gains act on the 20 calibrated anchor magnitudes. The
    # 10 gain vectors are independent: every named channel has a pivot in
    # K (disjoint nonempty anchor supports). Thus positive scaling removes
    # exactly 10 log-magnitude dimensions, not just at a sample point.
    need({WE[j][2] for j in K} == set(AXES), "independent channel gains")
    # Fix matter norm / canonical kinetic metric. Double the vacuum vertex
    # factor, then use one positive gain per channel to restore its original
    # squared Frobenius norm 8. Work entirely with rational SQUARED moduli.
    ref = [F(1) for _ in WE]
    raw = [F(4 if 0 in (a, b) else 1) for a, b, _ in WE]
    total = {
        k: sum((x for x, e in zip(raw, WE, strict=True) if e[2] == k), F(0))
        for k in AXES
    }
    norm = [x * 4 / total[e[2]] for x, e in zip(raw, WE, strict=True)]
    need(
        norm == powers(c.lift, [norm[j] for j in K]),
        "calibrated example still in reference orbit",
    )
    for k in AXES:
        vals = [x for x, e in zip(norm, WE, strict=True) if e[2] == k]
        need(2 * sum(vals) == 8, "fixed Frobenius norm")
        if k == (0, True):
            need(
                sorted(vals) == [F(4, 7)] * 3 + [F(16, 7)],
                "squared single-channel singular values, each twice",
            )

    def gram_diagonal(weights: list[F]) -> list[F]:
        # Each channel is a partial matching, so B_k† B_k is diagonal.
        return [
            sum(
                (x for x, (a, b, _) in zip(weights, WE, strict=True) if m in (a, b)),
                F(0),
            )
            for m in EVEN
        ]

    baseline, changed = gram_diagonal(ref), gram_diagonal(norm)
    need(
        baseline == [5] * 16 and changed[0] == F(80, 7) and sum(changed) == 80,
        "unitary-invariant separation",
    )
    # K=sum B_k†B_k is unchanged by a unitary change of channel basis and
    # undergoes unitary similarity under a unitary matter congruence.
    # If one named channel were the sole mass source with fixed coupling
    # and canonical kinetic terms, the Takagi singular-value ratio would
    # be 2 here rather than 1. No identification with observed masses.


def zero_control() -> None:
    # A stronger warning than a single surviving edge: all ten channels
    # remain nonzero, but share an eight-dimensional supporting subspace.
    keep = {0, 3, 5, 6, 9, 18, 29, 30}
    retained = [(a, b, k) for a, b, k in WE if a in keep and b in keep]
    need(
        len(keep) == 8
        and len(retained) == 11
        and {k for _, _, k in retained} == set(AXES),
        "zero-edge support escape",
    )
    need(
        {v for a, b, _ in retained for v in (a, b)} == keep,
        "common kernel of dimension at least eight",
    )
    # The full reference has an invertible reciprocal-axis sum. This
    # ablation can never have rank >8, hence cannot be GL-equivalent.


def main() -> None:
    cert = certificate()
    check_normalizer(cert)
    metric_controls(cert)
    zero_control()
    print(
        "40 NONZERO complex edge weights: no rank 10 iff the ratio to the reference is a diagonal rescaling."
    )
    print(
        "Two integral minors (-1,+1); 20 independent edge coordinates, branch-free Laurent normalization."
    )
    print(
        "With phases alone: 20 free positive magnitudes; calibrating all channel norms still leaves 10."
    )
    print(
        "Equal channel norms: reference Gram eigenvalues all 5; counterexample has 80/7 with the same pencil ranks."
    )
    print(
        "Allowing zeros: 11 edges keep all 10 channels on 8 states, so no rank 10 even outside the full orbit."
    )


if __name__ == "__main__":
    main()
