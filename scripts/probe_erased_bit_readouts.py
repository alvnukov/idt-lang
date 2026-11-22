"""Exact readouts on eight cube preparations, with the last-read axis retained.

In d=3 strict cyclic ballot survival requires the first two comparison bits
to be positive and leaves the last bit fair. The accepted (vertex, last axis)
therefore encodes a uniformly random incident edge and an independent fair
endpoint. The erasure choice is independent of the preparation. The vertex
alone forgets the edge. The laws are compared below.

For normalized affine rows p_j(n) = a_j + g_j·n, positivity on the cube gives
sum_i |g_ji| <= a_j. Write D_i = sum_j |g_ji|. An adjacent input pair differing
in bit i has output TV D_i and edge-channel TV 2/3, so D_i <= 2/3 is necessary.
It suffices: send D_i to the two rows k != i of capacity 1/3 each. Singletons
have capacity 2/3, while any two or three columns reach all rows; their mass
is at most sum_i D_i <= 1. Split each g_ji in these proportions, scale by 3,
and give every edge row intercepts at least its absolute slope sums. Remaining
effect and edge intercept deficits are nonnegative and have equal totals.

For qubit effects E_j = a_j(I + r_j·sigma) and supplied Bloch vectors n/sqrt(3),
g_j = a_j r_j/sqrt(3), ||r_j||_2 <= 1. Thus D_i <= 1/sqrt(3) < 2/3, and the
same argument over the reals covers all finite qubit POVMs on these eight
preparations. The replay itself checks rational fixtures, not every POVM. Its
decoder depends on the whole POVM, not the preparation; no universal state
space, noncontextual effect response, or derivation of quantum rules follows.
"""

from collections import Counter, deque
from collections.abc import Mapping
from fractions import Fraction as F
from itertools import accumulate, combinations, permutations, product
from math import prod
from typing import TypeVar

Point = tuple[int, int, int]
Signal = tuple[int, int, int]
Effect = tuple[F, tuple[F, ...]]
Law = tuple[F, ...]
T = TypeVar("T")

AXES = (0, 1, 2)
SIGNS = (-1, 1)
CUBE = tuple((x, y, z) for x, y, z in product(SIGNS, repeat=3))
VISIBLE = ((1, 2), (0, 2), (0, 1))
EDGES = tuple((k, x, y) for k in AXES for x, y in product(SIGNS, repeat=2))
BITS = tuple((i, x) for i in AXES for x in SIGNS)


def check(condition: bool, message: str) -> None:
    if not condition:
        raise RuntimeError(message)


def edge(k: int, n: Point) -> Signal:
    i, j = VISIBLE[k]
    return k, n[i], n[j]


def distance(left: dict[T, F], right: dict[T, F]) -> F:
    return (
        sum((abs(left.get(s, F(0)) - right.get(s, F(0))) for s in left | right), F(0))
        / 2
    )


def replay_channels() -> None:
    for n in CUBE:
        heralds: Counter[tuple[Point, int]] = Counter()
        for v in CUBE:
            for start in AXES:
                order = tuple((start + i) % 3 for i in AXES)
                if all(s > 0 for s in accumulate(n[i] * v[i] for i in order)):
                    heralds[v, order[-1]] += 1
        independent = {
            (v, k): F(1, 6) for v in CUBE for k in AXES if edge(k, n) == edge(k, v)
        }
        check(
            heralds.total() == 6
            and {s: F(c, heralds.total()) for s, c in heralds.items()} == independent,
            "ballot joint differs from erased bit and independent endpoint",
        )
        for v in CUBE:
            count = sum(heralds[v, k] for k in AXES)
            check(
                F(count, 6) == F(max(sum(n[i] * v[i] for i in AXES), 0), 6),
                "vertex marginal",
            )
    for n, m in combinations(CUBE, 2):
        if sum(x != y for x, y in zip(n, m, strict=True)) != 1:
            continue
        bit_tv = distance(
            {(i, n[i]): F(1, 3) for i in AXES}, {(i, m[i]): F(1, 3) for i in AXES}
        )
        edge_tv = distance(
            {edge(k, n): F(1, 3) for k in AXES}, {edge(k, m): F(1, 3) for k in AXES}
        )
        check((bit_tv, edge_tv) == (F(1, 3), F(2, 3)), "wrong adjacent-input TV")


def apply_channel(weights: dict[T, F], decoder: Mapping[T, Law]) -> Law:
    return tuple(
        sum((weights[s] * decoder[s][j] for s in weights), F(0))
        for j in range(len(next(iter(decoder.values()))))
    )


def probabilities(effects: tuple[Effect, ...], n: Point) -> Law:
    return tuple(a + sum(g[i] * n[i] for i in AXES) for a, g in effects)


def tetra_effects(words: tuple[Point, ...]) -> tuple[Effect, ...]:
    return tuple((F(1, 4), tuple(F(x, 12) for x in word)) for word in words)


def verify_bits(tetrahedra: tuple[tuple[Point, ...], ...]) -> None:
    for words in (*((m, (-m[0], -m[1], -m[2])) for m in CUBE), *tetrahedra):
        matches = len(words) // 2
        decoder = {
            (i, x): tuple(F(int(x == w[i]), matches) for w in words) for i, x in BITS
        }
        effects = tuple(
            (F(1, len(words)), tuple(F(x, 3 * len(words)) for x in w)) for w in words
        )
        for n in CUBE:
            check(
                apply_channel({(i, n[i]): F(1, 3) for i in AXES}, decoder)
                == probabilities(effects, n),
                "one-bit match decoder differs from aligned target",
            )
    axis_decoder = {
        (i, x): (F(1 + x, 2), F(1 - x, 2)) if i == 0 else (F(1, 2), F(1, 2))
        for i, x in BITS
    }
    for n in CUBE:
        plus = F(1, 2) + F(n[0], 6)
        check(
            apply_channel({(i, n[i]): F(1, 3) for i in AXES}, axis_decoder)
            == (plus, 1 - plus),
            "one-bit Cartesian response did not attain its TV bound",
        )
    check(F(1, 9) < F(1, 3), "Cartesian projective TV 1/sqrt(3) must exceed bit TV 1/3")


def allocate(masses: tuple[F, ...]) -> list[list[F]]:
    """Exact augmenting paths: vertices 0..2 are bits, 3..5 erasure rows."""
    source, sink = 6, 7
    residual = [[F(0) for _ in range(8)] for _ in range(8)]
    for i in AXES:
        residual[source][i] = masses[i]
        residual[3 + i][sink] = F(1, 3)
        for k in VISIBLE[i]:
            residual[i][3 + k] = F(1)
    while True:
        parents = {source: source}
        queue = deque([source])
        while queue and sink not in parents:
            u = queue.popleft()
            for v, cap in enumerate(residual[u]):
                if cap > 0 and v not in parents:
                    parents[v] = u
                    queue.append(v)
        if sink not in parents:
            break
        path = []
        v = sink
        while v != source:
            u = parents[v]
            path.append((u, v))
            v = u
        amount = min(residual[u][v] for u, v in path)
        for u, v in path:
            residual[u][v] -= amount
            residual[v][u] += amount
    check(
        all(residual[source][i] == 0 for i in AXES), "admissible cuts did not fill flow"
    )
    return [[residual[3 + k][i] for i in AXES] for k in AXES]


def edge_decoder(effects: tuple[Effect, ...]) -> dict[Signal, Law]:
    if (
        sum(a for a, _ in effects) != 1
        or any(len(g) != 3 or sum(map(abs, g)) > a for a, g in effects)
        or any(sum(g[i] for _, g in effects) != 0 for i in AXES)
    ):
        raise ValueError("not a normalized positive affine table on the cube")
    masses = tuple(sum((abs(g[i]) for _, g in effects), F(0)) for i in AXES)
    if any(mass > F(2, 3) for mass in masses):
        raise ValueError("adjacent-input TV exceeds 2/3")
    allocation = allocate(masses)
    slopes = [
        [
            [
                3 * allocation[k][i] * g[i] / masses[i] if masses[i] else F(0)
                for i in AXES
            ]
            for k in AXES
        ]
        for _, g in effects
    ]
    intercepts = [[sum(map(abs, row), F(0)) for row in effect] for effect in slopes]
    needs = [1 - sum(effect[k] for effect in intercepts) for k in AXES]
    check(all(need >= 0 for need in needs), "negative edge intercept slack")
    for (a, _), base in zip(effects, intercepts, strict=True):
        remaining = 3 * a - sum(base)
        check(remaining >= 0, "negative effect intercept slack")
        for k in AXES:
            obtained = min(remaining, needs[k])
            base[k] += obtained
            needs[k] -= obtained
            remaining -= obtained
        check(remaining == 0, "unfilled effect intercept slack")
    check(all(need == 0 for need in needs), "unfilled edge intercept slack")
    decoder = {}
    for k, x, y in EDGES:
        i, h = VISIBLE[k]
        row = tuple(
            b[k] + s[k][i] * x + s[k][h] * y
            for b, s in zip(intercepts, slopes, strict=True)
        )
        check(
            all(p >= 0 for p in row) and sum(row) == 1,
            "invalid pointwise edge decoder row",
        )
        decoder[k, x, y] = row
    return decoder


def verify_edges(effects: tuple[Effect, ...]) -> None:
    decoder = edge_decoder(effects)
    for n in CUBE:
        weights = {edge(k, n): F(1, 3) for k in AXES}
        check(
            apply_channel(weights, decoder) == probabilities(effects, n),
            "edge decoder differs from target",
        )


def main() -> None:
    replay_channels()
    tetrahedra = tuple(tuple(v for v in CUBE if prod(v) == parity) for parity in SIGNS)
    verify_bits(tetrahedra)
    print(
        "d=3: 8 ballot joints equal erased-bit edge with independent endpoint; adjacent edge TV=2/3"
    )
    print(
        "one bit: 8 aligned projectives and both cube tetrahedra exact; Cartesian TV ceiling 1/3 < 1/sqrt(3)"
    )
    for words in tetrahedra:
        for i, j, k in permutations(AXES):
            verify_edges(tetra_effects(tuple((v[i], v[j], v[k]) for v in words)))
    # Proper rotations: a planar 3/5,4/5 turn and a generic quaternion rotation.
    rotations = (
        (5, ((3, -4, 0), (4, 3, 0), (0, 0, 5))),
        (15, ((-10, 2, 11), (10, -5, 10), (5, 14, 2))),
    )
    for den, matrix in rotations:
        for words in tetrahedra:
            verify_edges(
                tuple(
                    (
                        F(1, 4),
                        tuple(
                            F(sum(r[i] * v[i] for i in AXES), 12 * den) for r in matrix
                        ),
                    )
                    for v in words
                )
            )
    verify_edges(
        tuple(
            (F(a, 20), tuple(F(x, 120) for x in g))
            for a, g in zip(
                (2, 3, 4, 5, 6),
                ((2, -3, 1), (-1, 2, 5), (2, 4, -2), (-5, -2, -3), (2, -1, -1)),
                strict=True,
            )
        )
    )
    # Saturates both the singleton cut D_0 = 2/3 and the total cut sum_i D_i = 1.
    verify_edges(
        tuple(
            (F(a, 6), (F(x, 6), F(y, 6), F(0)))
            for a, x, y in ((2, 2, 0), (2, -2, 0), (1, 0, 1), (1, 0, -1))
        )
    )
    print(
        "edge: aligned/permuted + rationally rotated tetrahedra, asymmetric five outcomes, and saturated cuts exact"
    )
    copy_bit = tuple((F(1, 2), (F(x, 2), F(0), F(0))) for x in SIGNS)
    try:
        edge_decoder(copy_bit)
    except ValueError as error:
        check(str(error) == "adjacent-input TV exceeds 2/3", "wrong copy-bit rejection")
    else:
        raise RuntimeError("out-of-scope exact copy-bit received a decoder")
    print(
        "negative control: exact copy has adjacent TV=1, above sharp edge ceiling 2/3"
    )


if __name__ == "__main__":
    main()
