"""Exact, low-cost consistency test for independent normalized pure source states.

Two Gram matrices in a common *labeled* source order define the same
internal-blind distinguishability data if they differ only by rephasing
individual input rays. This suffices for identical passive bosonic output
probabilities under the supplied permutation/Born rule. No claim is made
for mixed/correlated sources, internal-resolving detectors, missing data,
or inference from noisy empirical frequencies.
"""

from __future__ import annotations

import argparse
import json
import sys
from collections import deque
from dataclasses import dataclass
from fractions import Fraction
from itertools import pairwise
from pathlib import Path

if not __package__:
    sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
from scripts.gaussian_dyadic_words import ONE, ZERO, Gaussian, Matrix, g


def validated(matrix: Matrix) -> None:
    n = len(matrix)
    if not n or any(len(row) != n for row in matrix):
        raise ValueError("nonempty square Gram matrix required")
    if any(
        matrix[i][i] != ONE
        or any(matrix[i][j] != matrix[j][i].star() for j in range(n))
        for i in range(n)
    ):
        raise ValueError("normalized Hermitian Gram matrix required")
    # Exact PSD Schur test; a zero diagonal in a positive matrix requires a
    # zero row. Singular Gram matrices are valid and must NOT be rejected.
    m = matrix
    while m:
        d = m[0][0]
        if d.im or d.re < 0 or (d == ZERO and any(z != ZERO for z in m[0])):
            raise ValueError("Gram matrix is not positive semidefinite")
        k = g(1 / d.re) if d != ZERO else ZERO
        m = tuple(
            tuple(m[i][j] - m[i][0] * k * m[0][j] for j in range(1, len(m)))
            for i in range(1, len(m))
        )


@dataclass(frozen=True)
class Comparison:
    kind: str
    witness: tuple[int, ...]
    phases: tuple[Gaussian, ...]


def cycle_path(i: int, j: int, parent: dict[int, int]) -> tuple[int, ...]:
    def climb(v: int) -> list[int]:
        nodes = [v]
        while parent[v] != v:
            v = parent[v]
            nodes.append(v)
        return nodes

    a, b = climb(i), climb(j)
    where = set(b)
    common = next(k for k in a if k in where)
    return (*a[: a.index(common) + 1], *reversed(b[: b.index(common)]), i)


def compare(a: Matrix, b: Matrix) -> Comparison:
    validated(a)
    validated(b)
    n = len(a)
    if len(b) != n:
        raise ValueError("source labels must already have been matched")
    for i in range(n):
        for j in range(i + 1, n):
            if a[i][j].norm2() != b[i][j].norm2():
                return Comparison("pair-magnitude", (i, j), ())
    phase: dict[int, Gaussian] = {}
    parent: dict[int, int] = {}
    for root in range(n):
        if root in phase:
            continue
        phase[root], parent[root] = ONE, root
        q = deque((root,))
        while q:
            i = q.popleft()
            for j in range(n):
                z = a[i][j]
                if i == j or z == ZERO:
                    continue
                v = phase[i] * b[i][j] * z.star() * g(1 / z.norm2())
                if j not in phase:
                    phase[j], parent[j] = v, i
                    q.append(j)
                elif phase[j] != v:
                    return Comparison("cycle-phase", cycle_path(i, j, parent), ())
    return Comparison("rephasing-equivalent", (), tuple(phase[i] for i in range(n)))


def loop_value(m: Matrix, closed: tuple[int, ...]) -> Gaussian:
    if len(closed) < 3 or closed[0] != closed[-1]:
        raise ValueError("closed overlap loop required")
    result = ONE
    for i, j in pairwise(closed):
        result = result * m[i][j]
    return result


def parse_scalar(x: object) -> Gaussian:
    def fraction(v: object) -> Fraction:
        if isinstance(v, bool) or not isinstance(v, (int, str)):
            raise TypeError("use integers or rational strings, not floats")
        return Fraction(v)

    if isinstance(x, list) and len(x) == 2:
        return g(fraction(x[0]), fraction(x[1]))
    return g(fraction(x))


def parse_matrix(x: object) -> Matrix:
    if not isinstance(x, list) or not all(isinstance(row, list) for row in x):
        raise ValueError("list of matrix rows required")
    return tuple(tuple(parse_scalar(z) for z in row) for row in x)


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "input",
        type=Path,
        help="JSON with left and right normalized Gram matrices; entry: integer, rational string or [real,imaginary]",
    )
    args = parser.parse_args()
    try:
        obj = json.loads(args.input.read_text(encoding="utf-8"))
        if not isinstance(obj, dict) or set(obj) != {"left", "right"}:
            raise ValueError("expected exactly left and right")
        a, b = parse_matrix(obj["left"]), parse_matrix(obj["right"])
        result = compare(a, b)
    except (OSError, ValueError, TypeError, ZeroDivisionError) as exc:
        parser.error(str(exc))
    print(
        json.dumps(
            {
                "scope": "exact labeled pure-state Gram comparison",
                "result": result.kind,
                "witness": result.witness,
                "phases": [[str(x.re), str(x.im)] for x in result.phases],
            }
        )
    )


if __name__ == "__main__":
    main()
