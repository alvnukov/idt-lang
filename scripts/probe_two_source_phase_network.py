"""Finite paired-rail implementation of a two-source complex-composition test.

Not a reconstruction from probabilities alone. Supply the complex tensor
rule, two independent encoded Bell-pair sources, local addressable controls
and complete output records. On Charlie's side use three logical modes:
the data occupy two, and a third vacuum path completes a single binary
analyzer. EVERY final port has an assigned sign. No selected analyzer
herald, restart, infinite word, fitted parameter or discarded outcome.

We use the functional defined in Renou et al., arXiv:2101.10873, with
the authors' three pairs zx,zy,xy and four Bell
outcomes. The real independent-source upper bound 7.6605 is their reported
bound, not an SDP rederived here. The observable tensor factors and
spatially independent sources are not implied by a single multiport table.
"""

from __future__ import annotations

import sys
from collections import deque
from fractions import Fraction as F
from functools import cache
from itertools import product
from math import isqrt
from pathlib import Path

if not __package__:
    sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
from scripts.gaussian_dyadic_words import (
    ONE,
    ZERO,
    Gaussian,
    I,
    Matrix,
    apply,
    eye,
    g,
    run,
    synthesize,
    synthesize_isometry,
)

Z = ((ONE, ZERO), (ZERO, g(-1)))
X = ((ZERO, ONE), (ONE, ZERO))
Y = ((ZERO, g(0, -1)), (I, ZERO))
AXES = (Z, X, Y)
AXIS_PAIRS = ((0, 1), (0, 2), (1, 2))
BOUND = F(76605, 10000)
BitPair = tuple[int, int]
Outcome = tuple[int, int, int, int]
Table = dict[Outcome, F]  # (Alice sign, Bell b1, Bell b2, Charlie sign)
Experiment = dict[tuple[int, int], Table]


def need(ok: bool, why: str) -> None:
    if not ok:
        raise ArithmeticError(why)


def adj(a: Matrix) -> Matrix:
    return tuple(tuple(z.star() for z in col) for col in zip(*a, strict=True))


def gram(v: tuple[Gaussian, ...]) -> Matrix:
    return tuple(tuple(x * y.star() for y in v) for x in v)


def mm(a: Matrix, b: Matrix) -> Matrix:
    return tuple(
        tuple(
            sum((x * y for x, y in zip(row, col, strict=True)), ZERO)
            for col in zip(*b, strict=True)
        )
        for row in a
    )


def effect(obs: Matrix, sign: int) -> Matrix:
    return tuple(
        tuple(g(F(1, 2)) * (g(int(j == k)) + g(sign) * v) for k, v in enumerate(row))
        for j, row in enumerate(obs)
    )


def observable(positive: Matrix) -> Matrix:
    return tuple(
        tuple(g(2) * v - g(int(j == k)) for k, v in enumerate(row))
        for j, row in enumerate(positive)
    )


@cache
def cliffords() -> tuple[Matrix, ...]:
    seen = {eye(2)}
    queue = deque(seen)
    while queue:
        u = queue.popleft()
        for op in (("T", 0, 1), ("i", 0, 0)):
            w = apply(u, op)
            if w not in seen:
                seen.add(w)
                queue.append(w)
                need(len(seen) <= 96, "unexpected two-port group")
    need(len(seen) == 96, "two-port group incomplete")
    return tuple(seen)


def turned(u: Matrix, a: Matrix) -> Matrix:
    return mm(u, mm(a, adj(u)))


def charlie_settings(base: Matrix) -> tuple[Matrix, ...]:
    out = []
    for i, j in AXIS_PAIRS:
        for sign in (1, -1):
            wanted = tuple(tuple(g(sign) * x for x in row) for row in AXES[j])
            u = next(
                u
                for u in cliffords()
                if turned(u, Z) == AXES[i] and turned(u, X) == wanted
            )
            out.append(turned(u, base))
    return tuple(out)


def bell_ket(b1: int, b2: int) -> tuple[Gaussian, ...]:
    # Common phase difference from conventional real 1/sqrt(2) is immaterial.
    half = g(F(1, 2), -F(1, 2))
    return tuple(
        half * g((-1) ** (b1 * j)) if k == j ^ b2 else ZERO
        for j, k in product(range(2), repeat=2)
    )


def network_probability(alice: Matrix, bob: Matrix, charlie: Matrix) -> F:
    """Contract the PRODUCT of two prepared Bell pairs directly; no remote Bell-state shortcut.

    In tensor order A,B1,B2,C the four nonzero components have indices
    (j,j,k,k) and the same phase/magnitude. Their projector entries are 1/4.
    """
    value = sum(
        (
            alice[j][r] * bob[2 * j + k][2 * r + s] * charlie[k][s]
            for j, k, r, s in product(range(2), repeat=4)
        ),
        ZERO,
    ) * g(F(1, 4))
    need(value.im == 0 and 0 <= value.re <= 1, "nonprobability")
    return value.re


def distributions(
    base: Matrix,
    *,
    erase_imaginary: bool = False,
    mirror_alice: bool = False,
    mirror_charlie: bool = False,
) -> Experiment:
    def use(a: Matrix, mirror: bool) -> Matrix:
        if erase_imaginary:
            return tuple(tuple(g(v.re) for v in row) for row in a)
        return tuple(tuple(v.star() for v in row) for row in a) if mirror else a

    a_settings = [use(a, mirror_alice) for a in AXES]
    c_settings = [use(a, mirror_charlie) for a in charlie_settings(base)]
    bell = {(b1, b2): gram(bell_ket(b1, b2)) for b1, b2 in product(range(2), repeat=2)}
    records: Experiment = {}
    for x, a in enumerate(a_settings):
        for z, c in enumerate(c_settings):
            table: Table = {}
            for l, (b1, b2), r in product((-1, 1), bell, (-1, 1)):
                table[l, b1, b2, r] = network_probability(
                    effect(a, l), bell[b1, b2], effect(c, r)
                )
            need(sum(table.values()) == 1, "lost final output")
            for b1, b2 in bell:
                need(
                    sum(table[l, b1, b2, r] for l, r in product((-1, 1), repeat=2))
                    == F(1, 4),
                    "Bell branch reweighting",
                )
            records[x, z] = table
    return records


def functional(records: Experiment) -> F:
    value = F(0)
    for pair, (i, j) in enumerate(AXIS_PAIRS):
        for idx, (x, setting, sign) in enumerate(
            (
                (i, 2 * pair, 1),
                (i, 2 * pair + 1, 1),
                (j, 2 * pair, 1),
                (j, 2 * pair + 1, -1),
            )
        ):
            axis = i if idx < 2 else j
            for (a, b1, b2, c), p in records[x, setting].items():
                signs = ((-1) ** b2, (-1) ** b1, -((-1) ** (b1 + b2)))
                value += sign * signs[axis] * a * c * p
    return value


def analyzer(ket: tuple[Gaussian, ...]) -> Matrix:
    # Prepare this single native output axis, then use the inverse word to
    # measure it: '+' iff port zero, '-' on BOTH other ports.
    column = tuple((v,) for v in ket)
    word = synthesize_isometry(column)
    prep = run(eye(3), word)
    need(tuple(row[0] for row in prep) == ket, "native analyzer axis")
    physical = adj(prep)
    positive = mm(adj((physical[0][:2],)), (physical[0][:2],))
    negative = mm(
        adj(tuple(row[:2] for row in physical[1:])),
        tuple(row[:2] for row in physical[1:]),
    )
    need(
        all(
            positive[j][k] + negative[j][k] == eye(2)[j][k]
            for j, k in product(range(2), repeat=2)
        ),
        "incorrect all-output grouping",
    )
    return observable(positive)


def best_reference_face(
    k: int, *, spare: bool
) -> tuple[F, tuple[int, int, int, int, int]]:
    """Max Z+X contrast in this rank-one output-row contract; no experimental data.

    The four data numerator components can be nonnegative for this maximum:
    replacing by absolute values preserves norms and increases their dot
    product. The unobserved-coordinate squared norm must be one Gaussian
    integer norm (or zero without a spare). The final spare output is
    physically counted as negative, not postselected away.
    """
    if not 0 <= k <= 8:
        raise ValueError("bounded exhaustive numerator search k=0..8")
    d = 1 << k
    pairs = [
        (a, b, a * a + b * b)
        for a in range(isqrt(d) + 1)
        for b in range(isqrt(d - a * a) + 1)
    ]
    norms = {n for _, _, n in pairs} if spare else {0}
    val, nums = max(
        (aa - bb + 2 * (a * c + b * e), (a, b, c, e, d - aa - bb))
        for a, b, aa in pairs
        for c, e, bb in pairs
        if d - aa - bb in norms
    )
    return F(val, d), nums


def main() -> None:
    phi = tuple((x,) for x in bell_ket(0, 0))
    src = synthesize_isometry(phi)
    need(run(tuple(row[:1] for row in eye(4)), src) == phi, "each independent source")
    measurement = tuple(
        tuple(x.star() for x in bell_ket(b1, b2))
        for b1, b2 in product(range(2), repeat=2)
    )
    need(
        run(eye(4), synthesize(measurement)) == measurement, "native Bob Bell analyzer"
    )
    values = []
    for k in range(7):
        face, _ = best_reference_face(k, spare=True)
        bare, _ = best_reference_face(k, spare=False)
        need(bare == 1, "unassisted two-mode control")
        values.append(6 * face)
    need(
        values == [6, 6, 6, F(27, 4), F(63, 8), F(129, 16), F(267, 32)],
        "finite face maxima",
    )
    ket = (g(F(3, 4), F(2, 4)), g(F(1, 4), F(1, 4)), g(F(1, 4)))
    base = analyzer(ket)
    standard = distributions(base)
    score = functional(standard)
    erased = functional(distributions(base, erase_imaginary=True))
    need(
        score == F(63, 8) > BOUND and erased == F(43, 8) < BOUND,
        "two-source score/erasure controls",
    )
    one_mirror = distributions(base, mirror_alice=True)
    require_same = distributions(base, mirror_alice=True, mirror_charlie=True)
    need(
        require_same == standard
        and distributions(base, mirror_charlie=True) == one_mirror,
        "real sources and Bell effects: only relative chirality",
    )
    mirrored = functional(one_mirror)
    need(
        mirrored == F(23, 8) and erased == (score + mirrored) / 2,
        "relative orientation witness",
    )
    print(
        f"Independent encoded Bell pairs; all 18 setting pairs and 288 joint outcome cells "
        f"retained. Finite score={score}, naive entrywise-real erasure={erased}."
    )
    print(
        "Best 6×(Z+X) face under three-mode row denominator (1+i)^k, k=0..6:",
        ", ".join(str(v) for v in values),
    )
    print(
        f"Comparator: published real network upper bound {BOUND} (not recomputed). "
        f"Uniform TV error <{(score - BOUND) / 24} per active setting pair preserves separation."
    )
    print(
        "Supplied complex tensor product, independent encoded sources, calibrated local "
        "operations and complete readout; not a derivation of composition or new data."
    )
    print(
        "One relative phase conjugation gives 23/8; simultaneous conjugation leaves every cell unchanged. Independent fair signs give 43/8. A settings-independent mismatch probability h gives 63/8-5h, above the imported comparator only for h<0.0429."
    )


if __name__ == "__main__":
    main()
