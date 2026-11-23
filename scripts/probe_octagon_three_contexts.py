"""Smallest *supplied* three-matching packet incidence with octagonal faces.

Acceptance uses only: connected simple cubic incidence with labeled perfect
matchings A,B,C, eight sites on EVERY bicolored cycle, and uncolored girth
at least six. "Smallest" minimizes the size of a finite connected component
in this class. No commutator, sign, W, or detector requirement enters selection.

AB octagons tile the sites, so the size is a multiple of eight. A C edge
inside an AB octagon either duplicates an edge or closes a cycle of length
at most five. Thus eight sites cannot work; on sixteen sites C must connect
the two rings via a bijection f. Each ring can be indexed so its even starts
point forward under A; this is bookkeeping, not a spatial embedding.

Write circular distance as D. A circuit shorter than eight that uses cross
edges uses exactly two: the number is even, and successive cross edges must
be separated by at least one ring edge. Thus girth >= 6 requires
D(i,j)+D(f(i),f(j)) >= 4. In particular every one-step increment mod 8
lies in {3,4,5}; sums of consecutive increments must have distance >= 2.
Of possible sums 6..10, only 6 and 10 qualify, requiring equal steps 3,3
or 5,5. Hence f(i)=s*i+d with constant s in {3,5}. Both slopes do give
girth six (distance-two pairs map to distance-two pairs).

For the lower-layer start i put e=(-1)^i. The word ACAC first moves by e,
crosses, moves by -e*(-1)^d on the upper ring, and crosses back. Its net
offset mod 8 is e*(1-s*(-1)^d), since s is its own inverse. BCBC gives
the negative offset. Thus only s*(-1)^d = 5 mod 8 gives opposite-site
second returns; on the other branch the offset has magnitude two and those
bicolored circuits have length sixteen. Exhaustion checks both layers.

Words below run LEFT TO RIGHT. The raw states are one 11 packet among 00;
each context supplies one matching, with a unique eligible four-bit pair
complement. Complex structure below means only a real linear operator whose
square is minus identity on opposite-site occupancy differences. An address
is not a signed amplitude. Nothing selects this topology, component size,
matching labels, physical time, complex state space, or Born probabilities.
"""

from __future__ import annotations

import json
from collections import Counter, deque
from collections.abc import Iterator, Sequence
from itertools import permutations
from typing import TypedDict

RING = tuple(range(8))
PAIRS = ("AB", "AC", "BC")
A8 = tuple(i ^ 1 for i in RING)
B8 = tuple((i + (1 if i % 2 else -1)) % 8 for i in RING)
DIST = tuple(tuple(min((i-j) % 8, (j-i) % 8) for j in RING) for i in RING)
INDEX_PAIRS = tuple((i, j, DIST[i][j]) for i in RING for j in range(i))
Perm = tuple[int, ...]
Maps = dict[str, Perm]
Matching = tuple[tuple[int, int], ...]


class GraphStats(TypedDict):
    component_size: int
    girth: int


class SingleOctagon(TypedDict):
    joint_counts: dict[str, int]
    both_identity_and_W_squared_Z: int
    simple_cubic_girth_at_least_six: int


class TwoOctagons(TypedDict):
    tested: int
    girth_counts: dict[int, int]
    all_bicolored_octagons: int
    accepted: int
    minimum_connected_component_size: int
    accepted_affine_parameters: list[list[int]]
    colored_isomorphism_classes: int
    uncolored_isomorphic_rival: dict[str, list[int]]


class MinimalAction(TypedDict):
    raw_addresses: int
    common_fixed_point_free_central_Z: bool
    W_commutes_with_A_B_C: bool
    W_squared_equals_Z: bool
    opposite_difference_dimension: int
    signed_square: str


class DoubleCover(GraphStats):
    bicolored_lengths: dict[str, list[int]]
    from_zero: dict[str, int]


class ProbeReport(TypedDict):
    single_octagon: SingleOctagon
    two_octagons: TwoOctagons
    minimal_action: MinimalAction
    double_cover: DoubleCover
    scope: str


def require(condition: bool, reason: str) -> None:
    if not condition:
        raise ValueError(reason)


def action(maps: Maps, word: str) -> Perm:
    positions = tuple(range(len(maps["A"])))
    for letter in word:
        step = maps[letter]
        positions = tuple(step[x] for x in positions)
    return positions


def matchings(sites: Sequence[int]) -> Iterator[Matching]:
    """All labeled perfect involutions, including those overlapping A or B."""
    if not sites:
        yield ()
        return
    first, *rest = sites
    for k, other in enumerate(rest):
        for edges in matchings(rest[:k] + rest[k+1:]):
            yield ((first, other),) + edges


def bicolored_lengths(maps: Maps, pair: str) -> list[int]:
    """Count alternating cycles in edges, including double-edge length two."""
    seen, lengths = set(), []
    for i in range(len(maps["A"])):
        if i in seen:
            continue
        x, length = i, 0
        while True:
            seen.add(x)
            x = maps[pair[length % 2]][x]
            length += 1
            if x == i:
                break
        lengths.append(length)
    return sorted(lengths)


def graph_stats(maps: Maps) -> GraphStats:
    """Validate a supplied simple cubic graph; measure component zero and girth."""
    n = len(maps["A"])
    adj = [tuple(m[v] for m in maps.values()) for v in range(n)]
    require(all(len(set(ns)) == 3 and v not in ns for v, ns in enumerate(adj)),
            "graph is not simple cubic")
    girth, component_size = n + 1, 0
    for root in range(n):
        parent: dict[int, int | None] = {root: None}
        distance = {root: 0}
        queue = deque([root])
        while queue:
            x = queue.popleft()
            for y in adj[x]:
                if y not in distance:
                    parent[y], distance[y] = x, distance[x] + 1
                    queue.append(y)
                elif parent[x] != y and parent[y] != x:
                    girth = min(girth, distance[x] + distance[y] + 1)
        if root == 0:
            component_size = len(distance)
    return {"component_size": component_size, "girth": girth}


def single_octagon() -> SingleOctagon:
    identity = RING
    z = action({"A": A8, "B": B8}, "ABAB")
    kinds = {identity: "I", z: "Z"}
    joint: Counter[str] = Counter()
    commuting_control, legal = 0, 0
    for edges in matchings(RING):
        c = [0]*8
        for i, j in edges:
            c[i], c[j] = j, i
        maps = {"A": A8, "B": B8, "C": tuple(c)}
        kind = ",".join(kinds.get(action(maps, p*2), "other") for p in ("AC", "BC"))
        joint[kind] += 1
        commuting_control += kind == "I,I" and action(maps, "ABCABC") == z
        if all(c[i] not in (A8[i], B8[i]) for i in RING):
            legal += graph_stats(maps)["girth"] >= 6
    require(sum(joint.values()) == 105 and joint["Z,Z"] == 0 and
            joint["I,I"] == commuting_control == 5 and legal == 0, "8-site control")
    counts = {f"{a},{b}": joint[f"{a},{b}"] for a in ("I", "Z", "other")
              for b in ("I", "Z", "other")}
    return {"joint_counts": counts, "both_identity_and_W_squared_Z": commuting_control,
            "simple_cubic_girth_at_least_six": legal}


def two_rings(f: Perm) -> Maps:
    inverse = [0]*8
    for i, j in enumerate(f):
        inverse[j] = i
    return {"A": A8 + tuple(i+8 for i in A8), "B": B8 + tuple(i+8 for i in B8),
            "C": tuple(i+8 for i in f) + tuple(inverse)}


def ring_girth(f: Perm) -> int:
    # A two-cross circuit may take the shortest arc on each ring independently.
    return min(8, 2 + min(d + DIST[f[i]][f[j]] for i, j, d in INDEX_PAIRS))


def check_raw_actions(maps: Maps) -> None:
    n = len(maps["A"])
    packets = tuple(3 << (2*i) for i in range(n))
    for letter, mapping in maps.items():
        require(len(mapping) == n and all(0 <= j < n and i != j and mapping[j] == i
                for i, j in enumerate(mapping)), f"{letter} is not a perfect matching")
        masks = [packets[i] | packets[j] for i, j in enumerate(mapping) if i < j]
        for i, prepared in enumerate(packets):
            eligible = [m for m in masks if (m & prepared).bit_count() == 2]
            require(len(eligible) == 1 and (prepared ^ eligible[0]) == packets[mapping[i]],
                    "unique raw complement did not transport the packet")


def check_minimal_action(maps: Maps) -> MinimalAction:
    check_raw_actions(maps)
    z, w = action(maps, "ABAB"), action(maps, "ABC")
    require(all(action(maps, p*2) == z for p in PAIRS), "no common Z")
    require(all(z[i] != i and z[z[i]] == i for i in range(len(z))), "not free involution")
    for op in (z, w):
        for step in maps.values():
            require(all(step[op[i]] == op[step[i]] for i in range(len(op))),
                    "failed to commute with a context")
    require(all(w[w[i]] == z[i] for i in range(len(z))), "W squared differs from Z")
    # On b_i = e_i - e_{Z(i)}, W preserves this real span by commutation with Z.
    # W^2 b_i = b_{Z(i)} = -b_i; verify the ordered support of every basis image.
    basis = [(i, j) for i, j in enumerate(z) if i < j]
    require(all((w[w[i]], w[w[j]]) == (j, i) for i, j in basis), "signed square")
    return {"raw_addresses": len(z), "common_fixed_point_free_central_Z": True,
            "W_commutes_with_A_B_C": True, "W_squared_equals_Z": True,
            "opposite_difference_dimension": len(basis), "signed_square": "-identity"}


def check_relabel(source: Maps, target: Maps, relabel: Perm, colored: bool) -> None:
    require(set(relabel) == set(range(len(relabel))), "relabel is not a bijection")
    for v, u in enumerate(relabel):
        lhs = [relabel[source[k][v]] for k in "ABC"]
        rhs = [target[k][u] for k in "ABC"]
        require(lhs == rhs if colored else set(lhs) == set(rhs), "not an isomorphism")


def affine(s: int, d: int) -> Perm:
    return tuple((s*i + d) % 8 for i in RING)


def two_octagons() -> TwoOctagons:
    girths: Counter[int] = Counter()
    octagons = 0
    survivors: set[Perm] = set()
    wide_girth: set[Perm] = set()
    for f in permutations(RING):
        g = ring_girth(f)
        girths[g] += 1
        maps = two_rings(f)
        all_eight = all(bicolored_lengths(maps, p) == [8, 8] for p in ("AC", "BC"))
        octagons += all_eight
        if g >= 6:
            wide_girth.add(f)
            if all_eight:
                survivors.add(f)
    require(wide_girth == {affine(s, d) for s in (3, 5) for d in RING},
            "distance classification failed")
    params = [[s, d] for s in (3, 5) for d in RING if s*(-1)**d % 8 == 5]
    require(survivors == {affine(s, d) for s, d in params}, "colored classification")
    require(girths == {4: 37488, 5: 2816, 6: 16} and octagons == 552, "16-site census")
    reference = two_rings(affine(5, 0))
    require(graph_stats(reference) == {"component_size": 16, "girth": 6}
            and all(bicolored_lengths(reference, p) == [8, 8] for p in PAIRS),
            "reference does not witness an accepted component")
    for s, d in params:
        target = two_rings(affine(s, d))
        check_minimal_action(target)
        check_relabel(reference, target, RING + tuple(8 + (5*s*i + d) % 8 for i in RING),
                      colored=True)
    rival = two_rings(affine(3, 0))
    check_relabel(reference, rival, RING + tuple(8 + (-i) % 8 for i in RING), colored=False)
    rival_lengths = {p: bicolored_lengths(rival, p) for p in PAIRS}
    require(rival_lengths == {"AB": [8, 8], "AC": [16], "BC": [16]}, "rival control")
    return {"tested": sum(girths.values()), "girth_counts": dict(girths),
            "all_bicolored_octagons": octagons, "accepted": len(survivors),
            "minimum_connected_component_size": 16, "accepted_affine_parameters": params,
            "colored_isomorphism_classes": 1, "uncolored_isomorphic_rival": rival_lengths}


def lifted_control() -> Maps:
    """Vertex v+16*t; flip sheet only on the two specified lower A edges."""
    base = two_rings(affine(5, 0))
    flips = {0, 1, 4, 5}
    return {
        k: tuple(mapping[v] + 16*(sheet ^ (k == "A" and v in flips))
                 for sheet in (0, 1) for v in range(16))
        for k, mapping in base.items()
    }


def run_probe() -> ProbeReport:
    maps = lifted_control()
    check_raw_actions(maps)
    row = graph_stats(maps)
    lengths = {p: bicolored_lengths(maps, p) for p in PAIRS}
    endpoints = {p: action(maps, p)[0] for p in ("ABAB", "ACAC", "BCBC", "ABABC", "CABAB")}
    require(row == {"component_size": 32, "girth": 6} and all(v == [8]*4 for v in lengths.values()),
            "larger candidate does not meet local conditions")
    require(endpoints == {"ABAB": 20, "ACAC": 20, "BCBC": 4, "ABABC": 28, "CABAB": 12},
            "lift did not distinguish commonality and centrality")
    return {"single_octagon": single_octagon(), "two_octagons": two_octagons(),
            "minimal_action": check_minimal_action(two_rings(affine(5, 0))),
            "double_cover": {**row, "bicolored_lengths": lengths, "from_zero": endpoints},
            "scope": "Finite minimum with supplied labeled incidence; no quantum readout, "
                     "physical time, primitive selection of size, or universal common square."}


if __name__ == "__main__":
    print(json.dumps(run_probe(), indent=2, sort_keys=True))
