"""An n-photon cycle invisible to every proper source subset.

An independent pure internal state on each fixed, labeled input, the
bosonic exchange amplitude rule, lossless passive mixing, extra blank ports,
number-resolving detection with no internal-state resolution, and keeping
every output record are supplied. This is an exact benchmark of that model.
The two-layer comparison does NOT purport to reproduce a published apparatus.
"""

from __future__ import annotations

from fractions import Fraction as F
from itertools import permutations, product

from scripts.compare_exchange_phases import compare, loop_value
from scripts.gaussian_dyadic_words import (
    ONE,
    ZERO,
    Gaussian,
    I,
    Matrix,
    Move,
    eye,
    g,
    run,
)


def need(ok: bool, why: str) -> None:
    if not ok:
        raise ArithmeticError(why)


def ph(n: int) -> Gaussian:
    return (ONE, I, g(-1), g(0, -1))[n % 4]


def sources(n: int, phase: int) -> Matrix:
    if n < 3:
        raise ValueError("simple cycle needs at least three inputs")
    rays = []
    for i in range(n):
        j = (i + 1) % n
        col = tuple((r[i],) for r in eye(n))
        word: tuple[Move, ...] = (("T", i, j),) + (("i", j, j),) * (
            (1 + (phase if j == 0 else 0)) % 4
        )
        rays.append(tuple(x[0] for x in run(col, word)))
    return tuple(
        tuple(
            sum((x.star() * y for x, y in zip(a, b, strict=True)), ZERO) for b in rays
        )
        for a in rays
    )


def ring(n: int, analyzer: int) -> Matrix:
    if n < 3:
        raise ValueError("simple cycle needs at least three inputs")
    word: list[Move] = [("T", 2 * j, 2 * j + 1) for j in range(n)]
    word.extend((("i", 1, 1),) * (analyzer % 4))
    word.extend(("T", 2 * j, 2 * ((j - 1) % n) + 1) for j in range(n))
    return run(
        tuple(tuple(row[2 * j] for j in range(n)) for row in eye(2 * n)), tuple(word)
    )


def path_weight(
    u: Matrix, outputs: tuple[int, ...], route: tuple[int, ...]
) -> Gaussian:
    z = ONE
    for y, x in zip(outputs, route, strict=True):
        z = z * u[y][x]
    return z


def probability(
    u: Matrix, gram: Matrix, labels: tuple[int, ...], *, exhaustive: bool = False
) -> F:
    n = len(gram)
    outputs = tuple(
        2 * j if v == 0 else 2 * ((j - 1) % n) + 1 for j, v in enumerate(labels)
    )
    a = tuple(range(n))
    shift = tuple((j - 1) % n for j in range(n))
    paths = {
        p: path_weight(u, outputs, p)
        for p in (permutations(a) if exhaustive else (a, shift))
    }
    paths = {p: v for p, v in paths.items() if v != ZERO}
    need(set(paths) == {a, shift}, "not exactly two assignments")
    out = ZERO
    for p, z in paths.items():
        for q, w in paths.items():
            term = z * w.star()
            for j in range(n):
                term = term * gram[q[j]][p[j]]
            out = out + term
    need(out.im == 0 and 0 <= out.re <= 1, "invalid occupation probability")
    return out.re


def delete(m: Matrix, i: int) -> Matrix:
    return tuple(
        tuple(z for k, z in enumerate(r) if k != i) for j, r in enumerate(m) if j != i
    )


def experiment(n: int, phase: int, analyzer: int) -> tuple[F, F]:
    a, u = sources(n, phase), ring(n, analyzer)
    closed = (*range(n), 0)
    cycle = loop_value(a, closed)
    total = score = F(0)
    for mask in product(range(2), repeat=n):
        sig = (-1) ** mask.count(0)
        p = probability(u, a, mask, exhaustive=(n == 4))
        theoretical = F(2, 4**n) * (1 + sig * (ph(analyzer) * cycle.star()).re)
        need(p == theoretical, "sign/phase probability regression")
        total += p
        score += sig * p
    need(
        total == F(1, 2 ** (n - 1)), "postselection not phase independent in this model"
    )
    return total, score / total


def main() -> None:
    for n in (3, 4, 5, 6, 8, 12):
        base = sources(n, 0)
        changed = sources(n, 1)
        diff = compare(base, changed)
        need(
            diff.kind == "cycle-phase"
            and len(diff.witness) == n + 1
            and loop_value(base, diff.witness) != loop_value(changed, diff.witness),
            "wrong distinguishing cycle",
        )
        for i in range(n):
            need(
                compare(delete(base, i), delete(changed, i)).kind
                == "rephasing-equivalent",
                "proper subset can see the phase",
            )
    for n in (3, 4, 5, 6):
        for s, k in product(range(4), range(2)):
            tot, signal = experiment(n, s, k)
            need(abs(signal) <= F(1, 2**n), "maximum joint contrast")
            if n == 4 and k == 0 and s in (0, 2):
                print(
                    f"Four sources: phase={s} quarter-turns; one per station={tot}; signed conditional parity={signal}; all other records retained with score zero."
                )
    print(
        "All proper subsets of each checked 3,4,5,6,8,12-cycle are gauge-equivalent between variants. A spanning-tree test finds the missing labeled cycle without enumerating photon permutations. Real and imaginary quadratures use two fixed analyzer choices."
    )
    print(
        "Pure independent preparations, bosonic composition, squared-amplitude detector law and identical paths across contexts are supplied. Nonzero cycle phase does not by itself demonstrate a physical gauge field or an intrinsic click mechanism."
    )


if __name__ == "__main__":
    main()
