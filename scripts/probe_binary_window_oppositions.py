"""Exact finite probe of opposed contrasts on ONE binary worldline.

An L-window is a directed edge of the binary de Bruijn graph with L-1
memory bits. Bitwise complement supplies opposition. Constant windows are
discarded: they are self-loops, so this preserves the flow equation, but
normalizing retained counts is not normalization by all worldline ticks.

Periodic counts are nonnegative integer circulations. Open strings have an
endpoint defect and must not be treated as arbitrary periodic populations.
For L >= 2, the complement-odd circulation space has dimension
2**(L-2)-1; the complement-even space at fixed retained total has the same
dimension. The connected graph's incidence left kernel is constant: its
odd part is zero, and its even part has dimension one. This gives the rank
formula; the executable below checks L=2,...,6 over exact rationals.

This is a candidate finite classical encoding, not a physical derivation,
Lean proof, quantum state space, or exclusion of other one-bit mechanisms.
The symmetry exhaustion concerns vertex permutations of this particular
directed graph, plus reversal, NOT variable-radius block codes or resets.
"""

from __future__ import annotations

from collections.abc import Iterable
from fractions import Fraction as F
from itertools import permutations, product
from math import lcm

Matrix = tuple[tuple[F, ...], ...]
Counts = tuple[int, ...]


def need(condition: bool, message: str) -> None:
    if not condition:
        raise ArithmeticError(message)


def matrix(rows: Iterable[Iterable[int | F]]) -> Matrix:
    return tuple(tuple(F(x) for x in row) for row in rows)


def rref(rows: Matrix) -> tuple[Matrix, tuple[int, ...]]:
    work = [list(row) for row in rows]
    pivots: list[int] = []
    for col in range(len(rows[0])):
        pivot = next((i for i in range(len(pivots), len(work)) if work[i][col]), None)
        if pivot is None:
            continue
        row = len(pivots)
        work[row], work[pivot] = work[pivot], work[row]
        scale = work[row][col]
        work[row] = [x / scale for x in work[row]]
        for i in range(len(work)):
            if i != row:
                scale = work[i][col]
                work[i] = [
                    x - scale * y for x, y in zip(work[i], work[row], strict=True)
                ]
        pivots.append(col)
    return matrix(work), tuple(pivots)


def rank(rows: Matrix) -> int:
    return len(rref(rows)[1])


def nullspace(rows: Matrix) -> Matrix:
    reduced, pivots = rref(rows)
    basis: list[tuple[F, ...]] = []
    for col in range(len(rows[0])):
        if col in pivots:
            continue
        v = [F(0)] * len(rows[0])
        v[col] = F(1)
        for i, p in enumerate(pivots):
            v[p] = -reduced[i][col]
        basis.append(tuple(v))
    return tuple(basis)


def edges(length: int) -> tuple[int, ...]:
    return tuple(range(1, 2**length - 1))


def endpoints(word: int, length: int) -> tuple[int, int]:
    return word >> 1, word & (2 ** (length - 1) - 1)


def incidence(length: int, sign: int | None = None) -> Matrix:
    chosen = edges(length) if sign is None else tuple(range(1, 2 ** (length - 1)))
    mask = 2**length - 1

    def entry(vertex: int, edge: int) -> int:
        source, target = endpoints(edge, length)
        return int(vertex == source) - int(vertex == target)

    return matrix(
        (
            entry(v, e) + (0 if sign is None else sign * entry(v, e ^ mask))
            for e in chosen
        )
        for v in range(2 ** (length - 1))
    )


def apply(rows: Matrix, vector: tuple[int | F, ...]) -> tuple[F, ...]:
    return tuple(
        sum((x * y for x, y in zip(row, vector, strict=True)), F(0)) for row in rows
    )


def histogram(bits: tuple[int, ...], length: int, *, periodic: bool) -> Counts:
    need(bool(bits) and all(x in (0, 1) for x in bits), "binary nonempty input")
    counts = [0] * (2**length)
    stop = len(bits) if periodic else max(0, len(bits) - length + 1)
    for i in range(stop):
        word = 0
        for j in range(length):
            word = 2 * word + bits[(i + j) % len(bits)]
        counts[word] += 1
    return tuple(counts[1:-1])


def complement(counts: Counts) -> Counts:
    return counts[::-1]


def odd_part(counts: Counts) -> tuple[F, ...]:
    return tuple(F(x - y, 2) for x, y in zip(counts, complement(counts), strict=True))


def contrasts(counts: Counts) -> Counts:
    return tuple(counts[i] - counts[-1 - i] for i in range(len(counts) // 2))


def connected(length: int) -> bool:
    vertices = set(range(2 ** (length - 1)))
    for backward in (False, True):
        seen = {0}
        todo = [0]
        while todo:
            here = todo.pop()
            for e in edges(length):
                a, b = endpoints(e, length)
                if backward:
                    a, b = b, a
                if a == here and b not in seen:
                    seen.add(b)
                    todo.append(b)
        if seen != vertices:
            return False
    return True


def dimension_controls() -> list[dict[str, int]]:
    results: list[dict[str, int]] = []
    for length in range(2, 7):
        odd, even, full = incidence(length, -1), incidence(length, 1), incidence(length)
        pairs = len(odd[0])
        odd_dim = pairs - rank(odd)
        even_fixed = pairs - rank(even + (tuple(F(2) for _ in range(pairs)),))
        all_fixed = len(full[0]) - rank(full + (tuple(F(1) for _ in full[0]),))
        expected = 2 ** (length - 2) - 1
        need(connected(length), "nonconstant graph not strongly connected")
        need(odd_dim == even_fixed == expected, "opposition/even dimension formula")
        need(all_fixed == odd_dim + even_fixed, "fixed-total decomposition")
        need(
            not any(apply(full, (1,) * len(full[0]))), "uniform background not balanced"
        )
        results.append(
            {
                "L": length,
                "marks": len(full[0]),
                "odd": odd_dim,
                "even_fixed": even_fixed,
            }
        )
    return results


def endpoint_controls() -> None:
    for length in (3, 4):
        for n in range(length, 10):
            for bits in product((0, 1), repeat=n):
                counts = histogram(bits, length, periodic=False)
                first = sum(
                    x << (length - 2 - j) for j, x in enumerate(bits[: length - 1])
                )
                last = sum(
                    x << (length - 2 - j) for j, x in enumerate(bits[-length + 1 :])
                )
                boundary = tuple(
                    F(int(v == first) - int(v == last))
                    for v in range(2 ** (length - 1))
                )
                need(
                    apply(incidence(length), counts) == boundary,
                    "open endpoint identity",
                )
                odd_boundary = tuple(
                    (x - y) / 2 for x, y in zip(boundary, boundary[::-1], strict=True)
                )
                need(
                    apply(incidence(length), odd_part(counts)) == odd_boundary,
                    "odd endpoint correction",
                )
                closed = histogram(bits, length, periodic=True)
                need(not any(apply(incidence(length), closed)), "periodic flow")
    # Three isolated nonconstant L3 windows give the apparent three axes.
    # None is a balanced closed worldline; the independent information is
    # carried in their endpoints, not three stationary contrast directions.
    apparent = tuple(
        histogram(bits, 3, periodic=False) for bits in ((0, 0, 1), (0, 1, 0), (0, 1, 1))
    )
    need(
        rank(matrix(contrasts(c) for c in apparent)) == 3, "open negative control rank"
    )
    need(
        all(any(apply(incidence(3), c)) for c in apparent),
        "false closed negative control",
    )
    need(len(nullspace(incidence(3, -1))) == 1, "L3 only one closed contrast")


def euler_worldline(counts: Counts, length: int) -> tuple[int, ...]:
    need(all(x > 0 for x in counts), "Euler witness must have positive support")
    need(not any(apply(incidence(length), counts)), "Euler counts not balanced")
    remaining = list(counts)
    stack: list[tuple[int, int | None]] = [(0, None)]
    reverse_edges: list[int] = []
    while stack:
        vertex = stack[-1][0]
        chosen = next(
            (e for e in edges(length) if e >> 1 == vertex and remaining[e - 1]), None
        )
        if chosen is not None:
            remaining[chosen - 1] -= 1
            stack.append((endpoints(chosen, length)[1], chosen))
        else:
            _, incoming = stack.pop()
            if incoming is not None:
                reverse_edges.append(incoming)
    need(not any(remaining), "Euler component omitted")
    bits = tuple(e >> (length - 1) for e in reversed(reverse_edges))
    need(histogram(bits, length, periodic=True) == counts, "Euler histogram mismatch")
    return bits


def positive_realizability_controls() -> tuple[int, list[str]]:
    basis = nullspace(incidence(4, -1))
    integer_basis: list[Counts] = []
    for vector in basis:
        scale = lcm(*(x.denominator for x in vector))
        half = tuple(int(x * scale) for x in vector)
        integer_basis.append(half + tuple(-x for x in reversed(half)))
    need(len(integer_basis) == 3, "L4 odd basis")
    background = 1 + max(abs(x) for vector in integer_basis for x in vector)
    totals: set[int] = set()
    witnesses: list[str] = []
    for int_vector in integer_basis:
        for sign in (-1, 1):
            counts = tuple(background + sign * x for x in int_vector)
            totals.add(sum(counts))
            bits = euler_worldline(counts, 4)
            need(
                odd_part(counts) == tuple(F(sign * x) for x in int_vector),
                "lost signed displacement",
            )
            witnesses.append("".join(map(str, bits)))
    need(len(totals) == 1, "positive opposite witnesses must share fixed total")
    return background, witnesses


def feature_rows() -> Matrix:
    rows: list[list[F]] = [[], [], []]
    for e in edges(4):
        a, b, c, d = (1 - 2 * ((e >> j) & 1) for j in (3, 2, 1, 0))
        rows[0].append(F(a))
        rows[1].append(F(a * b * c))
        rows[2].append(F(a * b * d - a * c * d, 2))
    return matrix(rows)


def features(counts: Counts) -> tuple[F, ...]:
    total = sum(counts)
    need(total > 0, "features require retained windows")
    return tuple(x / total for x in apply(feature_rows(), counts))


def correlation_controls() -> list[tuple[str, tuple[F, ...]]]:
    # Named temporal statistics, not an isotropic frame:
    # M=<s0>, T=<s0*s1*s2>, A=(<s0*s1*s3>-<s0*s2*s3>)/2.
    strings = ("001", "0001", "001011")
    expected = (
        (F(1, 3), F(-1), F(0)),
        (F(1, 2), F(-1, 2), F(0)),
        (F(0), F(0), F(2, 3)),
    )
    out: list[tuple[str, tuple[F, ...]]] = []
    for word, target in zip(strings, expected, strict=True):
        bits = tuple(map(int, word))
        counts = histogram(bits, 4, periodic=True)
        got = features(counts)
        need(got == target, "short periodic witness")
        need(
            features(complement(counts)) == tuple(-x for x in got), "opposed statistics"
        )
        out.append((word, got))
    need(rank(matrix(v for _, v in out)) == 3, "three independent periodic contrasts")
    # Exact linear independence on the complete odd circulation space.
    basis = nullspace(incidence(4, -1))
    expanded = tuple(v + tuple(-x for x in reversed(v)) for v in basis)
    need(
        rank(matrix(apply(feature_rows(), v) for v in expanded)) == 3,
        "features incomplete on odd space",
    )
    for n in range(1, 9):
        for bits in product((0, 1), repeat=n):
            counts = histogram(bits, 4, periodic=True)
            if not sum(counts):
                continue
            m, t, a = features(counts)
            reversed_counts = histogram(bits[::-1], 4, periodic=True)
            need(
                features(reversed_counts) == (m, t, -a),
                "reversal has wrong feature action",
            )
            # Zero constant-window mass implies one relation on the four
            # stationary odd Walsh moments: 4M+2T+T013+T023=0.
            cross = F(0)
            for e, count in zip(edges(4), counts, strict=True):
                s0, s1, s2, s3 = (1 - 2 * ((e >> j) & 1) for j in (3, 2, 1, 0))
                cross += count * (s0 * s1 * s3 + s0 * s2 * s3)
            need(4 * m + 2 * t + cross / sum(counts) == 0, "odd Walsh constraint")
    return out


def reverse_word(word: int, width: int) -> int:
    return sum(((word >> i) & 1) << (width - 1 - i) for i in range(width))


def symmetry_controls() -> tuple[int, int]:
    relation = {endpoints(e, 4) for e in edges(4)}
    forward: list[tuple[int, ...]] = []
    backward: list[tuple[int, ...]] = []
    # Exhaust ALL 8! vertex permutations, not just guessed bit operations.
    for p in permutations(range(8)):
        if all((p[a], p[b]) in relation for a, b in relation):
            forward.append(p)
        if all((p[b], p[a]) in relation for a, b in relation):
            backward.append(p)
    identity, flip = tuple(range(8)), tuple(v ^ 7 for v in range(8))
    reversal = tuple(reverse_word(v, 3) for v in range(8))
    need(set(forward) == {identity, flip}, "unexpected directed graph automorphism")
    need(
        set(backward) == {reversal, tuple(v ^ 7 for v in reversal)},
        "unexpected graph anti-automorphism",
    )
    # The induced operations are I, -I, diag(1,1,-1), diag(-1,-1,1).
    # An order-four group cannot contain S3 or rotate three equal axes.
    need(len(forward) + len(backward) == 4, "extended finite symmetry size")
    return len(forward), len(backward)


def main() -> None:
    dimensions = dimension_controls()
    endpoint_controls()
    background, positive = positive_realizability_controls()
    short = correlation_controls()
    aut, anti = symmetry_controls()
    print(
        "PASS exact finite binary-window controls (ordinary exceptions, also active under -O)."
    )
    print(f"Dimensions L=2..6: {dimensions}")
    print("L3: six marks, ONE stationary odd contrast; open endpoints can fake three.")
    print("L4: fourteen marks, THREE odd + THREE even fixed-total directions, not 3+2.")
    print(
        f"Positive Euler realization: background={background}; six +/- basis witnesses; common length={len(positive[0])}."
    )
    for word, values in short:
        print(
            f"Periodic {word}: (mean, adjacent triple, reversal-odd triple difference/2)={tuple(map(str, values))}"
        )
    print(
        f"Exhausted 8! vertex permutations: {aut} automorphisms, {anti} anti-automorphisms."
    )
    print(
        "Complement negates all three statistics; reversal fixes two and negates one. No S3 axis symmetry follows."
    )
    print(
        "No claim of quantum structure or exclusion of variable-radius block codes, reset streams, or other one-bit mechanisms."
    )


if __name__ == "__main__":
    main()
