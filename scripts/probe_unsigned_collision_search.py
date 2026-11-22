"""Exhaustive search: does a transparent packet-level echo already force a mixer?

Packets are unordered pairs of DISTINCT marks on four addressed legs; there
are six packet species. A deterministic memoryless table maps each species
to one such packet. Two real rails per named observed port, fixed address
meaning across both ticks, and the exchange of the ports are supplied. No
signed lattice, Hilbert norm, linearity, hidden-pairing independence, Born
law or prescribed complementary rewrite enters the search. This is a finite
classification in a particularly restrictive microscopic model.
"""

from __future__ import annotations

from collections import Counter
from dataclasses import dataclass
from itertools import combinations, permutations, product

Edge = tuple[int, int]
Table = tuple[int, ...]
EDGES = tuple(combinations(range(4), 2))
INDEX = {e: i for i, e in enumerate(EDGES)}
INC = tuple(tuple(int(k in e) for k in range(4)) for e in EDGES)
COMP = tuple(
    next(i for i, f in enumerate(EDGES) if set(e).isdisjoint(f)) for e in EDGES
)
MATCHES = tuple((i, j) for i, j in enumerate(COMP) if i < j)
BY_PORT = tuple(sum(v[:2]) for v in INC)


def leg_table(p: tuple[int, ...]) -> Table:
    if sorted(p) != list(range(4)):
        raise ValueError("four-leg permutation required")
    return tuple(INDEX[min(p[a], p[b]), max(p[a], p[b])] for a, b in EDGES)


SWAP = leg_table((2, 3, 0, 1))
FIX = tuple(i for i, j in enumerate(SWAP) if i == j)
ID = tuple(range(6))


def after(a: Table, b: Table) -> Table:
    return tuple(a[x] for x in b)


PAIRS = tuple(
    tuple(tuple(x + y for x, y in zip(v, w, strict=True)) for w in INC) for v in INC
)
OVER = tuple(
    tuple(sum(x * y for x, y in zip(v, w, strict=True)) for w in INC) for v in INC
)


def check_table(f: Table) -> dict[str, bool]:
    """Six exact transitions are required; unavailable is not a predicted failure."""
    if len(f) != 6 or any(type(x) is not int or not 0 <= x < 6 for x in f):
        raise ValueError("complete six-entry unsigned edge table required")
    ff = after(f, f)
    outputs = {PAIRS[f[a]][f[b]] for a, b in MATCHES}
    packet_echo = ff == SWAP
    fixed = all(f[i] == i for i in FIX)
    coarse = all(BY_PORT[u] == BY_PORT[v] for u, v in zip(ff, SWAP, strict=True))
    coarse_fixed = all(BY_PORT[f[i]] == BY_PORT[i] for i in FIX)
    # All self-overlaps are two; pair overlap then checks the full Gram.
    metric = all(OVER[i][j] == OVER[f[i]][f[j]] for i, j in combinations(range(6), 2))
    return {
        "histogram_sufficient": len(outputs) == 1,
        "bijective": len(set(f)) == 6,
        "square_stock": metric,
        "raw_echo": packet_echo,
        "transparent_root": packet_echo and fixed,
        "coarse_echo": coarse,
        "coarse_transparent": coarse and coarse_fixed,
    }


@dataclass(frozen=True)
class Search:
    counts: dict[str, int]
    roots: tuple[Table, ...]
    coarse_nonraw: Table


def search() -> Search:
    count: Counter[str] = Counter()
    survivors = []
    roots = []
    mismatch = None
    preserving = set()
    for f in product(range(6), repeat=6):
        row = check_table(f)
        count["all"] += 1
        count.update(k for k, v in row.items() if v)
        if row["histogram_sufficient"] and row["bijective"]:
            preserving.add(f)
            count["bijective_histogram"] += 1
        if row["raw_echo"]:
            roots.append(f)
        if row["transparent_root"]:
            survivors.append(f)
        if row["coarse_transparent"] and not row["raw_echo"] and mismatch is None:
            mismatch = f
    leg = {leg_table(p) for p in permutations(range(4))}
    octahedral = leg | {after(COMP, p) for p in leg}
    rotation = leg_table((3, 0, 1, 2))
    both = {rotation, after(rotation, after(rotation, rotation))}
    need(
        preserving == octahedral and len(octahedral) == count["square_stock"] == 48,
        "reversible histogram classification",
    )
    need(
        set(roots) == both | {after(COMP, r) for r in both} and len(roots) == 4,
        "packet square roots",
    )
    need(
        set(survivors) == {after(COMP, r) for r in both} and len(survivors) == 2,
        "two transparent roots",
    )
    if mismatch is None:
        raise ArithmeticError("coarse comparison lacked its countercontrol")
    return Search(dict(count), tuple(survivors), mismatch)


def need(ok: bool, why: str) -> None:
    if not ok:
        raise ArithmeticError(why)


def main() -> None:
    s = search()
    print("All unordered two-mark collision tables:", s.counts)
    print(
        "From the complete two-tick raw echo alone only four tables remain. Fixing the two equal-input packet species leaves precisely complement followed by either orientation of one four-cycle. Neither a norm nor histogram closure was imposed."
    )
    print("Roots as six output species in the fixed lexicographic edge order:", s.roots)
    print(
        "Coarse two-port counts do not force the packet equation; explicit surviving nonroot:",
        s.coarse_nonraw,
    )
    print(
        "Finite, deterministic, memoryless distinct-edge packets with a supplied rail exchange; no inferred individual click, physical clock, Born rule or experimental status."
    )


if __name__ == "__main__":
    main()
