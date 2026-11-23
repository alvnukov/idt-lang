"""Frozen staggered two-helper topology holdout, with unscheduled raw moves.

Run: python3 -m scripts.probe_staggered_topology [--max-ring 8]
One JSON line per labelled graph/support assignment. Vertices and physical rails
are labelled. Mask bit e chooses AB (0) or BA (1), *reordering* endpoints to
match their fixed books. On an even ring the local left port is always i and
the right port i+1 modulo n. On the two trees no orientation is preferred.
Neither the incidence, the books nor metric geometry are reconstructed here.

Tree obstruction (argument, not a Lean artifact): at any degree >= 3 vertex
two incident edges have the same support choice. FORK_PATHS certifies the four
possibilities on those arms (vertex order: center, leaf, leaf). Embed a path
by holding the rest of the tree at T and all exterior private rails at 00;
no selected flip reads those rails. Both endpoints contain exactly one a and
one b. No native aa/bb move can ever become enabled: only the swap Ta/aT is
available, so b stays put. On an AB/AB fork the raw path moves b. On a BA/BA
fork it carries a across the central b, between different components after
deleting the center. The latter uses the tree assumption. Thus no choice of
these frozen supports makes the clean relation exact on a branching tree.
"""

import argparse
from array import array
from collections import Counter
from dataclasses import dataclass
from functools import cache, cached_property
from hashlib import sha256
from itertools import pairwise, product
import json

from scripts import probe_two_helper_staggered_search as frozen


BOOK = {"A": dict(zip("Tab", (1, 0, 2))), "B": dict(zip("Tab", (1, 0, 3)))}
TRIPLES = (((0, 1, 3), (1, 2, 3)), ((0, 1, 4), (0, 4, 5), (2, 3, 5), (2, 4, 5)))
Y = ((0, 1), (0, 2), (0, 3))
DOUBLE_Y = ((0, 1), (0, 2), (0, 3), (1, 4), (1, 5))
FORK_PATHS = {
    ("ABB", 0): (13, 63, 49),               # Tba -> Tab, AB/AB
    ("BAA", 0): (9, 59, 48, 62, 12, 47, 33),
    ("ABB", 3): (18, 214, 983, 199, 6),     # baT -> bTa, BA/BA
    ("BAA", 3): (19, 215, 22, 791, 7),
}


@dataclass(frozen=True)
class Graph:
    name: str
    books: str
    edges: tuple
    mask: int

    def __post_init__(self):
        if not self.books or set(self.books) - {"A", "B"}:
            raise ValueError("one book per labelled site required")
        if not 0 <= self.mask < (1 << len(self.edges)):
            raise ValueError("one binary support choice per edge")
        if len(set(tuple(sorted(edge)) for edge in self.edges)) != len(self.edges):
            raise ValueError("simple graph required")
        for i, j in self.edges:
            if not (0 <= i < len(self.books) and 0 <= j < len(self.books)) or self.books[i] == self.books[j]:
                raise ValueError("edge must join opposite books")

    @cached_property
    def ports(self):
        return tuple(
            (i, j) if self.books[i] == "AB"[self.mask >> e & 1] else (j, i)
            for e, (i, j) in enumerate(self.edges)
        )

    @cached_property
    def slots(self):
        nxt = 2 * len(self.books)
        result = []
        for e, (i, j) in enumerate(self.ports):
            data = (2*i, 2*i+1, 2*j, 2*j+1)
            if (self.mask >> e) & 1:
                data += (nxt, nxt + 1)
                nxt += 2
            result.append(data)
        return tuple(result)

    @property
    def width(self):
        return 2 * (len(self.books) + self.mask.bit_count())

    @cached_property
    def moves(self):
        return tuple(
            sum(1 << slots[k] for k in triple)
            for e, slots in enumerate(self.slots)
            for triple in TRIPLES[self.mask >> e & 1]
        )

    def encode(self, word):
        if len(word) != len(self.books):
            raise ValueError("word length mismatch")
        return sum(BOOK[b][c] << (2*i) for i, (b, c) in enumerate(zip(self.books, word)))


def holdouts(max_ring=6):
    if max_ring not in (4, 6, 8):
        raise ValueError("registered ring bounds are 4, 6, and 8")
    for n in range(4, max_ring+1, 2):
        yield Graph(
            f"ring{n}", "AB"*(n//2), tuple((i, (i+1) % n) for i in range(n)),
            sum(1 << i for i in range(1, n, 2)),
        )
    for name, colors, edges in (("Y", "ABBB", Y), ("double_Y", "ABBBAA", DOUBLE_Y)):
        for books in (colors, colors.translate(str.maketrans("AB", "BA"))):
            for mask in range(1 << len(edges)):
                yield Graph(name, books, edges, mask)


@cache
def native(n, edges):
    """Native adjacency calculated only on actual logical words, without raw labels."""
    mapping = {"aa": "bb", "bb": "aa", "Ta": "aT", "aT": "Ta"}
    words = tuple(map("".join, product("Tab", repeat=n)))
    labels = {}
    for seed in words:
        if seed in labels:
            continue
        labels[seed] = seed
        queue = [seed]
        for x in queue:
            for i, j in edges:
                out = mapping.get(x[i] + x[j])
                if out is not None:
                    chars = list(x)
                    chars[i], chars[j] = out
                    y = "".join(chars)
                    if y not in labels:
                        labels[y] = seed
                        queue.append(y)
    return words, labels


def spectator_check(graph):
    """Lift every isolated generator with all exterior rails set as sentinels.

    Since no lifted move reads or changes an exterior bit, this check of the
    support also applies to any exterior assignment. Shared endpoint sites are
    inside the support; no arbitrary parallel schedule is asserted.
    """
    count = 0
    for e, slots in enumerate(graph.slots):
        orientation = graph.mask >> e & 1
        outside = ((1 << graph.width) - 1) ^ sum(1 << j for j in slots)
        left, right = graph.ports[e]
        def lift(bits):
            return outside | sum((bits >> i & 1) << j for i, j in enumerate(slots))
        expected = {sum(1 << slots[k] for k in t) for t in TRIPLES[orientation]}
        for (u, v), path in frozen.GENERATOR_PATHS[orientation].items():
            raw = tuple(map(lift, path))
            endpoints = tuple(
                outside | BOOK[graph.books[left]][w[0]] << (2*left)
                | BOOK[graph.books[right]][w[1]] << (2*right)
                for w in (u, v)
            )
            if (raw[0], raw[-1]) != endpoints:
                raise ValueError("generator did not return literal private stock")
            for x, y in pairwise(raw):
                m = x ^ y
                if m not in expected or m & outside or x & m not in (0, m):
                    raise ValueError("generator touched a spectator or used a nonmove")
            count += 1
    return count


def partition_digest(words, labels):
    # Canonical representative = first seed in fixed product('Tab', repeat=n).
    return sha256("\n".join(w + ":" + labels[w] for w in words).encode("ascii")).hexdigest()


def shortest_extra(graph, clean, labels):
    """Multi-source BFS from all literal clean states, regardless of native label.

    Different-label frontiers witness an extra. Finish the first collision layer
    to distinguish odd/even path lengths; thus no shorter cross-label pair
    exists anywhere on this graph. A missing raw path cannot be replayed.
    """
    owner = {s: s for s in clean}
    parent = {s: None for s in clean}
    frontier = list(clean)
    while frontier:
        nxt = []
        best = None
        for x in frontier:
            for m in graph.moves:
                if x & m not in (0, m):
                    continue
                y = x ^ m
                if y not in owner:
                    owner[y] = owner[x]
                    parent[y] = x
                    nxt.append(y)
                elif labels[clean[owner[x]]] != labels[clean[owner[y]]]:
                    def trace(z):
                        route = []
                        while z is not None:
                            route.append(z)
                            z = parent[z]
                        return route
                    path = trace(x)[::-1] + trace(y)
                    if best is None or len(path) < len(best):
                        best = path
        if best is not None:
            return {"words": [clean[best[0]], clean[best[-1]]], "raw": best}
        frontier = nxt
    raise ValueError("partition reported an extra but no raw path found")


def compare(graph):
    """Compare both entire equivalence relations on 3^n labelled clean words."""
    words, target = native(len(graph.books), graph.edges)
    clean = {graph.encode(w): w for w in words}
    visited = bytearray(1 << graph.width)
    raw = {}
    moves = graph.moves
    for seed, first in clean.items():
        if visited[seed]:
            continue
        visited[seed] = 1
        queue = array("I", [seed])
        for x in queue:
            if x in clean:
                raw[clean[x]] = first
            for m in moves:
                if x & m in (0, m):
                    y = x ^ m
                    if not visited[y]:
                        visited[y] = 1
                        queue.append(y)
    def pairs(classes):
        return sum(s*(s-1)//2 for s in Counter(classes).values())
    both = pairs((raw[w], target[w]) for w in words)
    raw_n, native_n = pairs(raw.values()), pairs(target.values())
    missing, extra = native_n - both, raw_n - both
    if (raw == target) != (not missing and not extra):
        raise ValueError("canonical partition and pair-intersection verdicts disagree")
    missing_pair = None
    if missing:
        missing_pair = next((u, v) for u in words for v in words if target[u] == target[v] and raw[u] != raw[v])
    return {
        "name": graph.name, "books": graph.books, "edges": graph.edges, "mask": graph.mask,
        "native_pairs": native_n, "raw_pairs": raw_n, "missing_extra": (missing, extra),
        "native_partition_sha256": partition_digest(words, target),
        "raw_partition_sha256": partition_digest(words, raw),
        "missing_words": missing_pair, "shortest_extra": shortest_extra(graph, clean, target) if extra else None,
        "lifted_spectator_paths": spectator_check(graph),
    }


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--max-ring", type=int, choices=(4, 6, 8), default=6)
    args = parser.parse_args()
    for graph in holdouts(args.max_ring):
        print(json.dumps(compare(graph), separators=(",", ":")), flush=True)


if __name__ == "__main__":
    main()
