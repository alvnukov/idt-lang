"""Conditional additive charges of a marked folded-five carrier.

Construct the folded 5-cube, then discard its generating labels. Recover
the coordinate walls of the canonical bipartite double cover using only
distances from a chosen root lift and its five neighbours. A chosen
nonneighbour mark on the base picks exactly two of the five ports; no
intrinsic graph feature singles out the root, mark, or charge convention.

The antipodal quotient convention is explicit in arXiv:2307.03345, §2.1;
arXiv:1810.11284, §3 identifies the degree-five Clebsch graph with the
folded 5-cube. Only this graph relation is used from those papers.

Supplied laws: occupation additivity, zero vacuum, real or integer
charge invariant under the ordered root-and-mark stabilizer, and
sign reversal under the covering involution. Primitive integer units and
a sign are conventions. No gauge action, charge dynamics, particles,
measurement, or derivation of these laws is supplied by the graph.

For block sizes m,n the stabilizer makes the one-port weights constants
a,b within the respective blocks. Additivity gives q(x)=a*k_A+b*k_B.
Thus q(x)+q(antipode(x))=m*a+n*b even without oddness. Setting this sum
to zero selects one real line; its integer points are the multiples of
(-n/gcd(m,n),m/gcd(m,n)). Neither oddness nor the overall scale is learned.
"""

from __future__ import annotations

import json
from collections import Counter, deque
from collections.abc import Hashable
from fractions import Fraction
from itertools import permutations, product
from math import comb, gcd
from typing import TypeVar

N = 5
MASK = (1 << N) - 1
CUBE = tuple(range(MASK + 1))
PORT_BITS = tuple(1 << i for i in range(N))
V = TypeVar("V", bound=Hashable)
BaseGraph = dict[int, frozenset[int]]
Lift = tuple[int, int]
CoverGraph = dict[Lift, frozenset[Lift]]
Action = dict[int, int]
Occupation = tuple[int, int]


def need(condition, why):
    if not condition:
        raise ArithmeticError(why)


def anonymous_fixture() -> BaseGraph:
    # Each antipodal pair has one even representative since N is odd.
    # Even representatives of adjacent quotient vertices differ in four
    # bits. The resulting vertex names carry no usable cube coordinates.
    representatives = [u for u in CUBE if u.bit_count() % 2 == 0]
    names = {u: 37 + 11*((5*i+7) % len(representatives))
             for i, u in enumerate(representatives)}
    return {names[u]: frozenset(names[v] for v in representatives if (u ^ v).bit_count() == 4)
            for u in representatives}


def distances(graph: dict[V, frozenset[V]], root: V) -> dict[V, int]:
    dist, queue = {root: 0}, deque([root])
    while queue:
        u = queue.popleft()
        for v in graph[u]:
            if v not in dist:
                dist[v] = dist[u] + 1
                queue.append(v)
    return dist


def validate_base(graph: BaseGraph) -> None:
    need(len(graph) == 16, "base vertex count")
    for u, row in graph.items():
        need(u not in row and len(row) == 5, "base must be simple degree five")
        for v, other in graph.items():
            need((v in row) == (u in other), "asymmetric adjacency")
            if u != v:
                need(len(row & other) == (0 if v in row else 2), "base common-neighbour parameter")


def double_cover(graph: BaseGraph) -> CoverGraph:
    return {(u, p): frozenset((v, 1-p) for v in graph[u]) for u in graph for p in (0, 1)}


def recover_cover_coordinates(cover: CoverGraph, root: int) -> tuple[tuple[int, ...], dict[Lift, int]]:
    vacuum = (root, 0)
    lifted_ports = tuple(sorted(cover[vacuum]))
    vacuum_dist = distances(cover, vacuum)
    port_dists = tuple(distances(cover, p) for p in lifted_ports)
    need(len(vacuum_dist) == len(CUBE), "expected connected 32-vertex cover")
    coords = {}
    for vertex in cover:
        radial = vacuum_dist[vertex]
        need(all(abs(ds[vertex]-radial) == 1 for ds in port_dists), "not coordinate walls")
        coords[vertex] = sum(bit for bit, ds in zip(PORT_BITS, port_dists, strict=True) if ds[vertex] < radial)
        need(coords[vertex].bit_count() == radial and radial % 2 == vertex[1], "radial/parity mismatch")
    need(set(coords.values()) == set(CUBE) and coords[vacuum] == 0, "not a cube chart")
    for (v, p), x in coords.items():
        neighbours = {coords[w] for w in cover[v, p]}
        need(neighbours == {x ^ bit for bit in PORT_BITS}, "cover edges are not exactly the cube edges")
        need(coords[v, 1-p] == x ^ MASK, "cover involution is not the cube antipode")
    return tuple(v for v, _ in lifted_ports), coords


def base_chart(graph: BaseGraph, root: int) -> dict[int, int]:
    """Root, singleton ports, and nonneighbours indexed by common port pairs."""
    port_bits = dict(zip(sorted(graph[root]), PORT_BITS, strict=True))
    chart = {root: 0, **port_bits}
    for v in graph.keys() - chart.keys():
        chart[v] = sum(port_bits[u] for u in graph[root] & graph[v])
    need(len(set(chart.values())) == len(graph), "common port pairs do not identify the nonneighbours")
    return chart


def permute_mask(mask: int, image_bits: tuple[int, ...]) -> int:
    return sum(bit for source, bit in zip(PORT_BITS, image_bits, strict=True) if source & mask)


def all_base_automorphisms(graph: BaseGraph, root: int) -> list[Action]:
    # Any automorphism is determined by where it sends this root and each
    # port: the remaining vertices have distinct common-port-pair records.
    chart = base_chart(graph, root)
    reindexed = tuple({u: permute_mask(x, bits) for u, x in chart.items()}
                      for bits in permutations(PORT_BITS))
    automorphisms: list[Action] = []
    for target in graph:
        inverse_target = {x: v for v, x in base_chart(graph, target).items()}
        for indexed in reindexed:
            action = {u: inverse_target[x] for u, x in indexed.items()}
            need(len(set(action.values())) == len(graph), "not bijective")
            need(all({action[w] for w in graph[v]} == graph[action[v]] for v in graph),
                 "candidate root/port relabelling is not an automorphism")
            automorphisms.append(action)
    need(len({tuple(a[v] for v in graph) for a in automorphisms}) == 1920, "automorphism count")
    return automorphisms


def port_block(graph: BaseGraph, cover: CoverGraph, root: int, mark: int
               ) -> tuple[int, dict[Lift, int], tuple[int, ...]]:
    ports, coords = recover_cover_coordinates(cover, root)
    if mark in graph[root]:
        distinguished = {mark}
        sheet = 1  # the unique marked lift adjacent to the vacuum
    else:
        need(mark != root, "the mark must be distinct")
        distinguished = graph[root] & graph[mark]
        sheet = 0  # the unique lift two steps from the vacuum
    support = sum(bit for port, bit in zip(ports, PORT_BITS, strict=True) if port in distinguished)
    need(coords[mark, sheet] == support, "base port partition disagrees with marked cover lift")
    return support, coords, ports


def occupations(mask: int, block_b: int) -> Occupation:
    return (mask & (MASK ^ block_b)).bit_count(), (mask & block_b).bit_count()


def values_by_weight(block_b: int, a, b) -> dict[int, int | Fraction]:
    return {u: a*p + b*q for u in CUBE for p, q in (occupations(u, block_b),)}


def antipodal_odd(values: dict[int, int | Fraction]) -> bool:
    return all(values[u ^ MASK] == -values[u] for u in CUBE)


def occupation_additive(values: dict[int, int | Fraction]) -> bool:
    return all(values[u | v] == values[u] + values[v] for u, v in product(CUBE, repeat=2) if not u & v)


def audit_mark(
    graph: BaseGraph, cover: CoverGraph, actions: list[Action], root: int, mark: int,
) -> tuple[dict[str, object], int]:
    block, coords, ports = port_block(graph, cover, root, mark)
    size_b, size_a = block.bit_count(), N - block.bit_count()
    stabilizer = [a for a in actions if a[root] == root and a[mark] == mark]
    port_bits = dict(zip(ports, PORT_BITS, strict=True))
    perms = {tuple(port_bits[a[v]] for v in ports) for a in stabilizer}
    expected_perms = {p for p in permutations(PORT_BITS) if permute_mask(block, p) == block}
    need(perms == expected_perms, "incomplete or oversized marked stabilizer")
    for action in stabilizer:
        bits = tuple(port_bits[action[v]] for v in ports)
        need(all(coords[action[u], sheet] == permute_mask(x, bits) for (u, sheet), x in coords.items()),
             "base stabilizer does not lift to the recovered port action")
    for x in CUBE:
        actual = {permute_mask(x, p) for p in perms}
        expected = {u for u in CUBE if occupations(u, block) == occupations(x, block)}
        need(actual == expected, "marked occupation row is not one orbit")

    divisor = gcd(size_a, size_b)
    weights = (-(size_b//divisor), size_a//divisor)  # sign convention: the marked block is positive
    primitive = values_by_weight(block, *weights)
    need(primitive[0] == 0 and occupation_additive(primitive) and antipodal_odd(primitive), "primitive charge laws")
    # Scope-wide equivalence is algebraic: q(x) + q(x^MASK) is the
    # total of the five occupation weights for every x. Exact probes
    # include integer and noninteger scale examples, not a fit.
    for a, b in product((Fraction(-5, 3), -2, -1, 0, 1, 3, Fraction(5, 2)), repeat=2):
        proposal = values_by_weight(block, a, b)
        total = size_a*a + size_b*b
        need(all(proposal[x] + proposal[x ^ MASK] == total for x in CUBE), "nonconstant antipodal sum")
        need(antipodal_odd(proposal) == (total == 0), "neutrality and oddness diverged")
        if total == 0:
            need(a*weights[1] == b*weights[0], "not on primitive charge ray")

    sheet_rows: dict[str, list[dict[str, object]]] = {}
    for sheet, tag in ((0, "even"), (1, "odd")):
        counts = Counter((occupations(x, block), primitive[x]) for (_, s), x in coords.items() if s == sheet)
        sheet_rows[tag] = [{"occupation": list(occ), "multiplicity": count, "charge": charge}
                           for (occ, charge), count in sorted(counts.items())]
        need(sum(counts.values()) == 16, "sheet has wrong size")
        need(all(count == comb(size_a, p)*comb(size_b, q) for ((p, q), _), count in counts.items()),
             "orbit size disagrees with independent binomial count")
    return {"block_sizes": [size_a, size_b], "stabilizer_order": len(stabilizer),
            "neutrality_equation": f"{size_a}a+{size_b}b=0",
            "primitive_integer_weights_with_positive_mark_block": list(weights),
            "orbits": sheet_rows}, block


def countercontrols(block_b: int, root_preserving: list[Action], root_ports: tuple[int, ...]) -> dict[str, object]:
    primitive = values_by_weight(block_b, -2, 3)
    without_odd = values_by_weight(block_b, 1, 1)
    need(without_odd[0] == 0 and occupation_additive(without_odd) and not antipodal_odd(without_odd),
         "losing oddness should allow occupation weights outside the neutral ray")

    orbit_labels = {occupations(u, block_b) for u in CUBE}
    pairs = {(p, q) for p, q in orbit_labels if (p, q) < (3-p, 2-q)}
    need(len(pairs) == 6 and (0, 0) in pairs, "wrong antipodal occupation orbit pairing")
    free = sorted(pairs - {(0, 0)})
    for left in free:
        right = 3-left[0], 2-left[1]
        values = {u: int(occupations(u, block_b) == left) - int(occupations(u, block_b) == right)
                  for u in CUBE}
        need(values[0] == 0 and antipodal_odd(values), "independent orbit-pair parameter is not valid")
    nonlinear = {u: int(occupations(u, block_b) == (1, 0)) - int(occupations(u, block_b) == (2, 2))
                 for u in CUBE}
    need(antipodal_odd(nonlinear) and nonlinear[0] == 0 and not occupation_additive(nonlinear),
         "nonadditive odd witness failed")

    centered = {u: 2*u.bit_count()-N for u in CUBE}
    need(antipodal_odd(centered) and centered[0] == -N, "centered equal-weight affine countercontrol")
    need({a[root_ports[0]] for a in root_preserving} == set(root_ports), "unmarked root ports are not equivalent")
    need(any(primitive[u] != primitive[u ^ MASK] for u in CUBE), "primitive charge accidentally descends")

    # Translation by any port is a finite involution. Constant increments
    # on both traversals would satisfy 2*increment=0 in R or Z.
    steps = []
    for bit in PORT_BITS:
        flipped = {u: u ^ bit for u in CUBE}
        need(all(flipped[flipped[u]] == u for u in CUBE), "port toggle is not an involution")
        delta = {u: primitive[flipped[u]] - primitive[u] for u in CUBE}
        need(all(delta[flipped[u]] == -delta[u] for u in CUBE), "reverse edge increment mismatch")
        increments = set(delta.values())
        need(increments == {primitive[bit], -primitive[bit]} and len(increments) == 2,
             "occupation charge was mistaken for a constant path increment")
        steps.append(sorted(increments))
    return {
        "drop_oddness_keep_additivity_vacuum_example": {
            "weights": [1, 1], "antipodal_sum": without_odd[MASK],
        },
        "drop_neutrality_only": "not_independent_of_oddness_for_vacuum_anchored_additive_charge",
        "drop_additivity_keep_oddness_vacuum": {
            "free_orbit_pair_coefficients": len(free), "plus_one_occupation": [1, 0],
            "minus_one_occupation": [2, 2],
        },
        "allow_affine_offset_without_vacuum_normalization": {"equal_port_weight": 2, "vacuum_charge": -N},
        "same_on_both_sheets_plus_odd": "pointwise q=-q gives zero over the reals or integers",
        "unmarked_root_equal_port_weights_plus_odd": "5a=0 gives zero",
        "full_unrooted_automorphism_invariance": "transitivity and zero vacuum force zero",
        "path_increment_on_translation_involutions": {
            "constant_homomorphism": "zero because twice each generator increment is zero",
            "actual_occupation_increments_per_port": steps,
        },
    }


def probe() -> dict[str, object]:
    graph = anonymous_fixture()
    validate_base(graph)
    cover = double_cover(graph)
    root = min(graph)
    root_ports, _ = recover_cover_coordinates(cover, root)
    actions = all_base_automorphisms(graph, root)
    root_preserving = [a for a in actions if a[root] == root]
    adjacent, nonneighbor = min(graph[root]), min(graph.keys() - graph[root] - {root})
    ordered_adjacent = {(a[root], a[adjacent]) for a in actions}
    ordered_nonadjacent = {(a[root], a[nonneighbor]) for a in actions}
    need(len({a[root] for a in actions}) == 16 and len(root_preserving) == 120, "root symmetry")
    need(ordered_adjacent == {(v, w) for v in graph for w in graph[v]}, "ordered adjacent pairs are not equivalent")
    need(ordered_nonadjacent == {(v, w) for v in graph for w in graph.keys()-graph[v]-{v}},
         "ordered nonadjacent pairs are not equivalent")
    need({(a[root], p) for a in actions for p in (0, 1)} == cover.keys(), "unrooted cover symmetry")
    for v in graph:
        recover_cover_coordinates(cover, v)
    primary, block = audit_mark(graph, cover, actions, root, nonneighbor)
    alternative, _ = audit_mark(graph, cover, actions, root, adjacent)
    need(primary["block_sizes"] == [3, 2] and alternative["block_sizes"] == [4, 1], "mark block counts")
    swapped = [a for a in actions if (a[root], a[nonneighbor]) == (nonneighbor, root)]
    need(len(swapped) == primary["stabilizer_order"], "the nonneighbour pair is symmetric when unordered")
    _, root_coords = recover_cover_coordinates(cover, root)
    charge = values_by_weight(block, -2, 3)
    marked_value = charge[root_coords[nonneighbor, 0]]
    need(marked_value == 6 and marked_value != charge[root_coords[root, 0]],
         "pair exchange should not preserve the primitive ordered charge")
    controls = countercontrols(block, root_preserving, root_ports)
    controls["require_invariance_under_unordered_mark_exchange"] = {
        "primitive_charge_at_exchanged_vacuum": marked_value,
        "constraint_with_chosen_zero_vacuum": "2b=0, so neutrality also gives a=0",
    }
    return {
        "scope": "finite graph and conditional additive occupations only; no physical inference",
        "base": {"vertices": len(graph), "strongly_regular_parameters": [16, 5, 0, 2],
                 "automorphisms": len(actions), "root_stabilizer_order": len(root_preserving),
                 "ordered_nonneighbor_pair_orbit": len(ordered_nonadjacent),
                 "ordered_adjacent_pair_orbit": len(ordered_adjacent),
                 "nonneighbor_pair_exchanging_automorphisms": len(swapped)},
        "cover": {"vertices": len(cover), "is_cube": True, "deck_map": "antipode",
                  "coordinate_recovery": "distance comparison after choosing root lift and numbering its ports"},
        "root_nonneighbor": primary,
        "root_adjacent_control": alternative,
        "assumption_controls": controls,
    }


if __name__ == "__main__":
    print(json.dumps(probe(), sort_keys=True, separators=(",", ":")))
