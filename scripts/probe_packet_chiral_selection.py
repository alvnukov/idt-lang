"""Inverse anomaly filter on the candidate exterior representation, not a field derivation.

Assume five complex one-particle modes in a 3+2 split, ordinary exterior
powers, an additive tracer-free charge, space-time left Weyl fermions, and
the usual local SU(3)xSU(2)xU(1) anomaly cancellation tests in four space-time
dimensions (no inflow, extra heavy sector or modified cancellation).
Unlike the forward benchmark, do NOT assume even occupation or a family.
Enumerate every block subrepresentation that selects zero or one copy of
each of the 12 (p,q) exterior blocks, including empty and vectorlike models.
Global SU(2) parity is the ordinary doublet test, not a general bordism audit.
"""

from __future__ import annotations

from fractions import Fraction as F
from itertools import combinations, permutations, product
from math import comb, prod

Block = tuple[int, int]
Row = tuple[int, ...]
BLOCKS = tuple(product(range(4), range(3)))
# Choose positive representatives by even occupation, not as a selection
# rule: every complementary odd block is still independently enumerated.
REPS: tuple[Block, ...] = ((2, 0), (1, 1), (0, 2), (3, 1), (2, 2))


def require(ok: bool, reason: str) -> None:
    if not ok:
        raise ArithmeticError(reason)


def dual(b: Block) -> Block:
    return 3 - b[0], 2 - b[1]


def anomaly(b: Block, weights: tuple[int, int, int] = (0, -2, 3)) -> Row:
    p, q = b
    color, weak = comb(3, p), comb(2, q)
    shift, a, d = weights
    y = shift + a * p + d * q
    # All quadratic indices in units of a fundamental; conjugates have
    # opposite cubic SU3 index but the same quadratic index.
    cubic = (0, 1, -1, 0)[p]
    return (
        weak * cubic,
        weak * int(p in (1, 2)) * y,
        color * int(q == 1) * y,
        color * weak * y,
        color * weak * y**3,
        color * int(q == 1),
    )


def sum_rows(
    blocks: tuple[Block, ...], weights: tuple[int, int, int] = (0, -2, 3)
) -> Row:
    rows = [anomaly(b, weights) for b in blocks]
    return tuple(sum(r[j] for r in rows) for j in range(6))


def determinant(matrix: tuple[Row, ...]) -> int:
    n = len(matrix)
    return sum(
        (-1) ** sum(p[i] > p[j] for i, j in combinations(range(n), 2))
        * prod(matrix[i][p[i]] for i in range(n))
        for p in permutations(range(n))
    )


def kernel() -> int:
    cols = tuple(anomaly(b)[:5] for b in REPS)
    require(
        all(
            tuple(-x for x in c) == anomaly(dual(b))[:5]
            for b, c in zip(REPS, cols, strict=True)
        ),
        "not conjugate anomaly columns",
    )
    require(
        all(sum(c[j] for c in cols) == 0 for j in range(5)),
        "even-sign family not in kernel",
    )
    # The first four consistency rows already have rank four. Their column
    # sum is zero, so the integer kernel for arbitrary net multiplicities
    # is exactly the integral span of (1,1,1,1,1); no cutoff in this step.
    minor = determinant(tuple(tuple(c[j] for c in cols[:4]) for j in range(4)))
    require(minor != 0, "net chirality not fixed")
    require(
        all(
            determinant(tuple(tuple(c[j] for c in cols[:4]) for j in js)) != 0
            for js in combinations(range(5), 4)
        ),
        "single-filter omission changed rank",
    )
    return minor


def census() -> dict[int, int]:
    counts: dict[int, int] = {}
    for mask in range(1 << len(BLOCKS)):
        blocks = tuple(b for j, b in enumerate(BLOCKS) if mask & (1 << j))
        s = sum_rows(blocks)
        if any(s[:5]) or s[5] % 2:
            continue
        differences = tuple(int(b in blocks) - int(dual(b) in blocks) for b in REPS)
        require(len(set(differences)) == 1, "unbalanced chirality survived")
        k = differences[0]
        counts[k] = counts.get(k, 0) + 1
        if k:
            charged = tuple(b for b in blocks if anomaly(b)[3] != 0)
            require(
                sum(comb(3, p) * comb(2, q) for p, q in charged) == 15,
                "incomplete charged chiral family",
            )
    require(counts == {0: 128, 1: 4, -1: 4}, "4096-subrepresentation census")
    return counts


def offset_controls() -> None:
    even = tuple(b for b in BLOCKS if sum(b) % 2 == 0)
    fifteen = tuple(b for b in even if b != (0, 0))
    # If complement really denotes charge conjugation, twice the vacuum
    # offset is -(3a+2b). Use doubled units here to avoid half-integral input.
    # Every perturbative coefficient is a polynomial of degree <=3 in a,b.
    # A 4x4 evaluation grid establishes its polynomial identity in Q[a,b].
    for a, b in product(range(4), repeat=2):
        w = (-(3 * a + 2 * b), 2 * a, 2 * b)
        full = sum_rows(even, w)
        require(
            full[:5] == (0,) * 5 and full[5] % 2 == 0,
            "affine anomaly-free spinor plane",
        )
        reduced = sum_rows(fifteen, w)
        require(reduced[:5] == (0, 0, 0, -w[0], -(w[0] ** 3)), "charged vacuum removed")
    # Anomaly cancellation does not require selecting any chiral matter.
    require(
        sum_rows(()) == (0,) * 6 and sum_rows((REPS[0], dual(REPS[0])))[:5] == (0,) * 5,
        "vectorlike control",
    )
    require(
        sum_rows(tuple(b for b in BLOCKS if sum(b) in (0, 2)))[:5] != (0,) * 5,
        "truncated grades",
    )


def center_controls() -> None:
    # Label a central SU3 phase by u/3, a central SU2 sign by v/2 and a
    # U1 phase by t/6 (in turns). A fundamental-even grade-four dual makes
    # larger kernels impossible: it already detects the whole 5-slot action.
    even = tuple(b for b in BLOCKS if sum(b) % 2 == 0)
    kernel_points = []
    for u, v, t in product(range(3), range(2), range(6)):
        effects = tuple(
            (F(p * u, 3) + F(q * v, 2) + F(t * (-2 * p + 3 * q), 6)) % 1
            for p, q in even
        )
        if not any(effects):
            kernel_points.append((u, v, t))
    require(
        set(kernel_points) == {(t % 3, t % 2, t) for t in range(6)},
        "wrong six-element kernel",
    )


def main() -> None:
    minor = kernel()
    c = census()
    offset_controls()
    center_controls()
    print(
        f"All 4096 exterior-block subsets: {c[0]} anomaly-free vectorlike/neutral; {c[1]} chiral and {c[-1]} conjugate (two optional neutral labels). Nonzero integral net chirality is one common family multiple; rank-four minor {minor}."
    )
    print(
        "Parity was not a selection input. Chirality, local field consistency, exterior statistics, 3+2 gauge action and the additive charge are inputs. Neither handed orientation, number of copies nor neutral singlets are selected."
    )
    print(
        "Relax the neutral vacuum: full 16 supports an affine two-parameter anomaly-free plane. On the particular 15 with the vacuum omitted, mixed gravitational cancellation requires 3a+2b=0. The common sixfold central kernel on local multiplets does not determine the physical global gauge group."
    )


if __name__ == "__main__":
    main()
