"""Projective measurement alone need not force Born readout on native rays.

Domain: normalized Gaussian-dyadic columns and ALL square Gaussian-dyadic
orthonormal bases in three logical modes, with independently addressable
paired rails. Vertices are rays and unordered bases; an incidence edge means
membership. This is NOT the full complex qutrit projective space. The
infinite-tree argument and its physical limitations are in NATIVE_FRAME_RULES.md.
Finite generation, a separate exhaustive small-shell oracle, and a four-mode
parity obstruction are checked below. No fitted data or formal-proof status.
"""

from __future__ import annotations

import sys
from collections import Counter
from fractions import Fraction as F
from itertools import combinations, product
from math import isqrt
from pathlib import Path

if not __package__:
    sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
from scripts.gaussian_dyadic_words import (
    ZERO,
    Gaussian,
    eye,
    g,
    run,
    synthesize_isometry,
)

Ray = tuple[int, ...]  # integer real/imaginary numerator coordinates, modulo four units
Basis = tuple[Ray, ...]


def need(ok: bool, why: str) -> None:
    if not ok:
        raise ArithmeticError(why)


def turn(v: Ray) -> Ray:
    return tuple(
        value for r, i in zip(v[::2], v[1::2], strict=True) for value in (-i, r)
    )


def canonical(v: Ray) -> Ray:
    if not any(v):
        raise ValueError("zero is not a ray")
    while all((r - i) % 2 == 0 for r, i in zip(v[::2], v[1::2], strict=True)):
        v = tuple(
            value
            for r, i in zip(v[::2], v[1::2], strict=True)
            for value in ((r + i) // 2, (i - r) // 2)
        )
    u = turn(v)
    return max(v, u, tuple(-x for x in v), tuple(-x for x in u))


def level(v: Ray) -> int:
    n = sum(x * x for x in v)
    if not n or n & (n - 1):
        raise ValueError("not a normalized dyadic ray")
    return n.bit_length() - 1


def at(v: Ray, k: int) -> Ray:
    if k < level(v):
        raise ValueError("too small a common denominator")
    for _ in range(k - level(v)):
        v = tuple(x + y for x, y in zip(v, turn(v), strict=True))
    return v


def alternatives(a: Ray, b: Ray) -> tuple[tuple[Ray, Ray], tuple[Ray, Ray]]:
    k = max(level(a), level(b))
    x, y = at(a, k), at(b, k)

    def pair(y0: Ray) -> tuple[Ray, Ray]:
        # Both sums are divided by the same pi in normalized coordinates;
        # their integral numerators determine their canonical rays.
        return (
            canonical(tuple(p + q for p, q in zip(x, y0, strict=True))),
            canonical(tuple(p - q for p, q in zip(x, y0, strict=True))),
        )

    return pair(y), pair(turn(y))


def tree(kmax: int) -> tuple[set[Basis], dict[Ray, int]]:
    if not 0 <= kmax <= 8:
        raise ValueError("bounded replay levels 0..8")
    root = tuple(sorted(tuple(int(j == 2 * i) for j in range(6)) for i in range(3)))
    bases = {root}
    values = {v: int(i == 0) for i, v in enumerate(root)}
    front = [root]
    for k in range(kmax):
        new = []
        for basis in front:
            for v in basis:
                if level(v) != k:
                    continue
                a, b = (r for r in basis if r != v)
                for c, d in alternatives(a, b):
                    need(
                        c != d and c not in values and d not in values,
                        "cycle or duplicate",
                    )
                    need(level(c) == level(d) == k + 1, "incorrect child level")
                    child = tuple(sorted((v, c, d)))
                    need(child not in bases, "duplicate context")
                    bases.add(child)
                    new.append(child)
                    # Any choice of one child when the parent is false works.
                    values[c] = int(not values[v] and c < d)
                    values[d] = int(not values[v] and d < c)
        front = new
    need(
        all(sum(values[v] for v in b) == 1 for b in bases), "dispersion-free assignment"
    )
    need(
        len(values) == 4 ** (kmax + 1) - 1 and 2 * len(bases) == len(values) - 1,
        "tree shell count",
    )
    return bases, values


def shell(k: int) -> set[Ray]:
    # Independently enumerate every direction using six integer squares.
    if not 0 <= k <= 4:
        raise ValueError("independent exhaustive oracle restricted to levels 0..4")
    n = 2**k
    pairs: dict[int, list[tuple[int, int]]] = {}
    for r in range(-isqrt(n), isqrt(n) + 1):
        for i in range(-isqrt(n - r * r), isqrt(n - r * r) + 1):
            pairs.setdefault(r * r + i * i, []).append((r, i))
    return {
        canonical(a + b + c)
        for p, aa in pairs.items()
        for q, bb in pairs.items()
        for a, b, c in product(aa, bb, pairs.get(n - p - q, ()))
    }


def orthogonal(v: Ray, w: Ray) -> bool:
    a, b, c, d, e, f = v
    p, q, r, s, t, u = w
    return (
        a * p + b * q + c * r + d * s + e * t + f * u == 0
        and a * q - b * p + c * s - d * r + e * u - f * t == 0
    )


def all_bases(rays: set[Ray]) -> set[Basis]:
    ordered = sorted(rays)
    after = {
        r: {s for s in ordered[i + 1 :] if orthogonal(r, s)}
        for i, r in enumerate(ordered)
    }
    return {(r, s, t) for r in ordered for s in after[r] for t in after[r] & after[s]}


def parity_four() -> tuple[tuple[Ray, ...], tuple[tuple[int, ...], ...]]:
    # Real rays of norms 1,2,4 are natively normalizable, using the common
    # phase freedom of each basis column when the real normalization is sqrt(2).
    rays = tuple(
        v
        for v in product((-1, 0, 1), repeat=4)
        if sum(x * x for x in v) in (1, 2, 4) and next(x for x in v if x) == 1
    )
    edges = tuple(
        c
        for c in combinations(range(len(rays)), 4)
        if all(
            sum(x * y for x, y in zip(rays[i], rays[j], strict=True)) == 0
            for i, j in combinations(c, 2)
        )
    )
    # Exact GF(2) elimination, then enumerate this ten-dimensional kernel.
    pivots: dict[int, tuple[int, int]] = {}
    deps = []
    for j, c in enumerate(edges):
        x, w = sum(1 << i for i in c), 1 << j
        while x and x.bit_length() in pivots:
            a, b = pivots[x.bit_length()]
            x, w = x ^ a, w ^ b
        if x:
            pivots[x.bit_length()] = x, w
        else:
            deps.append(w)
    span = [0]
    for d in deps:
        span.extend([x ^ d for x in span])
    choice = min(
        (x for x in span if x.bit_count() % 2), key=lambda x: (x.bit_count(), x)
    )
    witness = tuple(c for j, c in enumerate(edges) if choice >> j & 1)
    counts = Counter(r for c in witness for r in c)
    need(
        (len(rays), len(edges), len(deps), len(witness)) == (24, 24, 10, 9)
        and len(counts) == 18
        and set(counts.values()) == {2},
        "four-mode parity witness",
    )
    return rays, witness


def normalized(nums: tuple[Gaussian, ...]) -> tuple[Gaussian, ...]:
    n = sum((x.norm2() for x in nums), F(0))
    need(n.denominator == 1 and n > 0 and int(n) & (int(n) - 1) == 0, "non-dyadic norm")
    for _ in range(int(n).bit_length() - 1):
        nums = tuple(g(F(1, 2), -F(1, 2)) * x for x in nums)
    return nums


def blank_port_pentagon() -> tuple[F, ...]:
    """A sharp four-mode comparison with a prepared state supported on three inputs.

    Adjacent listed events can be measured as two outputs of one compiled
    basis. No auxiliary click is discarded. On the three-input subspace the
    fourth listed event is an unsharp effect, not a bare projective qutrit ray.
    """
    real = ((1, 0, 0, 0), (0, 1, 0, 0), (1, 0, 1, 0), (-1, -1, 1, 1), (0, 1, 1, 0))
    rays = tuple(normalized(tuple(g(t) for t in v)) for v in real)
    psi = normalized((g(2, 1), g(1, 1), g(1), ZERO))
    # The fourth input path is blank even in the preparation word.
    prep = tuple((x,) for x in psi[:3])
    need(
        run(tuple(row[:1] for row in eye(3)), synthesize_isometry(prep)) == prep,
        "three-mode preparation",
    )
    p = tuple(
        sum((a.star() * b for a, b in zip(v, psi, strict=True)), ZERO).norm2()
        for v in rays
    )
    for i, v in enumerate(rays):
        cols = tuple(zip(v, rays[(i + 1) % 5], strict=True))
        u = run(eye(4), synthesize_isometry(cols))
        need(tuple(row[:2] for row in u) == cols, "adjacent-context compilation")
        measured = tuple(
            sum((x.star() * y for x, y in zip(col, psi, strict=True)), ZERO).norm2()
            for col in zip(*u, strict=True)
        )
        need(
            sum(measured) == 1 and measured[:2] == (p[i], p[(i + 1) % 5]),
            "all-output Born comparator",
        )
    bound = max(
        sum(bits)
        for bits in product((0, 1), repeat=5)
        if all(not (bits[i] and bits[(i + 1) % 5]) for i in range(5))
    )
    need(
        bound == 2
        and p == (F(5, 8), F(1, 4), F(5, 8), F(1, 4), F(5, 16))
        and sum(p) > bound,
        "five-event exclusivity comparison",
    )
    return p


def main() -> None:
    for k in range(5):
        exact = shell(k)
        b, f = tree(k)
        need(
            exact == set(f) and b == all_bases(exact), "independent whole-shell census"
        )
    b, f = tree(5)
    need(any(f[v] and level(v) == 1 for v in f), "non-Born true superposition")
    rays, witness = parity_four()
    pentagon = blank_port_pentagon()
    print(
        f"Qutrit projective controls: all {len(b)} bases on {len(f)} rays in levels ≤5 "
        "admit one context-independent 0/1 choice. Separate free enumeration through level 4."
    )
    print(
        f"Four logical modes: {len(witness)} bases on 18 of {len(rays)} native rays; "
        "each used ray occurs twice, but the number of basis clicks would be odd."
    )
    print(
        f"Five sharp adjacent-event pairs with one blank path and a three-mode input: "
        f"Born benchmark {sum(pentagon)} versus deterministic noncontextual ceiling 2."
    )
    print(
        "Valuations for projective qutrit bases do not supply dynamics or composite states; "
        "the four-mode obstruction excludes deterministic noncontextual rays, not Born alternatives in general."
    )


if __name__ == "__main__":
    main()
