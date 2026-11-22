"""Minimum degree from local two-step reunions and a genuine odd return.

Assume a finite connected simple triangle-free graph. Every non-backtracking
two-edge walk must have exactly one different two-edge route to the same
endpoint. No rule is imposed on vertex pairs that lack a two-edge route.

For adjacent u,v, square completion matches neighbours of u other than v
bijectively with neighbours of v other than u. The graph is then k-regular.
Fix a root and let x have depth i with an inward neighbour y. Each inward
neighbour z of y completes z--y--x to z--y'--x; y' has depth i-1 by its two
adjacencies. Distinct z give distinct y': otherwise y and y' have the
three common neighbours x,z,z', contradicting the same local rule. Thus
x has at least i inward neighbours by induction. Counting shell edges
gives i*s_i <= (k-i+1)*s_(i-1), hence s_i <= binom(k,i), diameter <= k,
and at most 2**k vertices. This proof works on the base or on its cover.

The canonical bipartite double cover inherits the local rule and degree.
It is connected exactly when a genuine odd-edge closed walk exists in
the base; the walk lifts from a vertex on one sheet to its other copy.
Thus v <= 2**(k-1) in the nonbipartite case. Independently, triangle
freeness and square completion give initial shells 1,k,binom(k,2).
These two inequalities exclude k<5; k=5 forces v=16 and diameter 2.
Each shell-two vertex names a pair of root ports. Its three shell-two
neighbours must be disjoint pairs, and there are exactly three candidates.
This forces the folded-five graph without a global nonneighbour rule.

Cartesian products preserve the local law: both steps in one factor
use that factor's alternative, and one step in each factor has the
other ordering as its unique alternative. An odd return in either
factor survives. A literal graph join is not this construction.

An anonymous observation recurring is not evidence of vertex equality.
The finite controls below audit the reasoning, not a physical detector,
selection of the root/marked pair, or a theory status.
"""

from __future__ import annotations

import json
from collections import Counter, deque
from collections.abc import Hashable, Iterable
from itertools import combinations, pairwise, permutations, product
from math import comb
from typing import TypeAlias, TypeVar

Node = TypeVar("Node", bound=Hashable)
Graph: TypeAlias = dict[Node, frozenset[Node]]


def need(condition, why):
    if not condition:
        raise ArithmeticError(why)


def undirected(vertices: Iterable[Node], edges: Iterable[tuple[Node, Node]]) -> Graph[Node]:
    graph: dict[Node, set[Node]] = {v: set() for v in vertices}
    for a, b in edges:
        graph[a].add(b)
        graph[b].add(a)
    return {v: frozenset(row) for v, row in graph.items()}


def cube(d: int) -> Graph[int]:
    return {x: frozenset(x ^ (1 << i) for i in range(d)) for x in range(1 << d)}


def folded_cube(d: int) -> Graph[int]:
    full = (1 << d) - 1
    quotient = {x: min(x, x ^ full) for x in range(1 << d)}
    return {x: frozenset(quotient[x ^ (1 << i)] for i in range(d))
            for x in sorted(set(quotient.values()))}


def cycle(n: int) -> Graph[int]:
    return undirected(range(n), ((i, (i+1) % n) for i in range(n)))


def cartesian(a, b):
    return {(u, v): frozenset({(x, v) for x in a[u]} | {(u, y) for y in b[v]})
            for u, v in product(a, b)}


def graph_join(a, b):
    side_a, side_b = {(0, u) for u in a}, {(1, v) for v in b}
    return ({(0, u): frozenset({(0, x) for x in a[u]} | side_b) for u in a}
            | {(1, v): frozenset({(1, y) for y in b[v]} | side_a) for v in b})


def double_cover(graph):
    return {(u, s): frozenset((v, 1-s) for v in row)
            for u, row in graph.items() for s in (0, 1)}


def breadth(graph: Graph[Node], source: Node) -> tuple[dict[Node, int], dict[Node, Node]]:
    dist, parent, queue = {source: 0}, {}, deque([source])
    while queue:
        u = queue.popleft()
        for v in sorted(graph[u], key=repr):
            if v not in dist:
                dist[v] = dist[u] + 1
                parent[v] = u
                queue.append(v)
    return dist, parent


def component_sizes(graph) -> list[int]:
    unseen = set(graph)
    sizes = []
    while unseen:
        seen, _ = breadth(graph, next(iter(unseen)))
        unseen.difference_update(seen)
        sizes.append(len(seen))
    return sorted(sizes)


def local_conditions(graph) -> dict[str, object]:
    need(all(u not in ns and all(u in graph[v] for v in ns) for u, ns in graph.items()),
         "fixture not simple and undirected")
    triangular = any(graph[u] & graph[v] for u in graph for v in graph[u])
    alternative_counts = Counter(len(graph[u] & graph[v])-1
                                 for ns in graph.values() for u, v in combinations(ns, 2))
    return {"component_sizes": component_sizes(graph), "triangle_free": not triangular,
            "unique_other_two_edge_route": set(alternative_counts) <= {1},
            "other_route_count_histogram": dict(sorted(alternative_counts.items()))}


def across_edge(graph, u, v, x):
    """Other intermediate on x--u--v, computed from the local reunion."""
    alternatives = (graph[x] & graph[v]) - {u}
    need(u in graph[x] and v in graph[u] and v != x and len(alternatives) == 1,
         "does not have the specified one other two-edge route")
    return next(iter(alternatives))


def audit_regular_from_squares(graph) -> int:
    for u, row in graph.items():
        for v in row:
            pairs = {x: across_edge(graph, u, v, x) for x in row - {v}}
            need(set(pairs.values()) == graph[v] - {u}, "square completion not onto")
            need(all(across_edge(graph, v, u, y) == x for x, y in pairs.items()), "square completion not inverse")
    degrees = {len(ns) for ns in graph.values()}
    need(len(degrees) == 1, "connected local graph is not regular")
    return next(iter(degrees))


def audit_shells(graph, degree: int) -> dict[str, object]:
    profiles = set()
    descent_squares = 0
    for root in graph:
        depth, _ = breadth(graph, root)
        diameter = max(depth.values())
        shells = [{v for v, i in depth.items() if i == j} for j in range(diameter+1)]
        sizes = tuple(map(len, shells))
        profiles.add(sizes)
        need(sizes == tuple(Counter(depth.values())[i] for i in range(diameter+1)), "shell census")
        if degree >= 2:
            need(sizes[:3] == (1, degree, comb(degree, 2)), "first two shells not forced as expected")
        need(diameter <= degree and all(size <= comb(degree, i) for i, size in enumerate(sizes)),
             "binomial shell bound or diameter violated")
        for i in range(1, len(shells)):
            a, b = shells[i-1], shells[i]
            counted = sum(len(graph[x] & a) for x in b)
            need(counted == sum(len(graph[y] & b) for y in a), "miscounted shell edges")
            need(i*len(b) <= counted <= (degree-i+1)*len(a), "incorrect two-sided shell edge bound")
            for x in b:
                inner = graph[x] & a
                need(len(inner) >= i, "pointwise inward degree smaller than depth")
                deeper = shells[i-2] if i >= 2 else set()
                for y in inner:
                    predecessors = graph[y] & deeper
                    lifts = {across_edge(graph, y, x, z) for z in predecessors}
                    need(len(lifts) == len(predecessors), "distinct predecessor squares collided")
                    need(lifts <= inner - {y}, "completed squares failed to stay at the inward depth")
                    descent_squares += len(lifts)
    return {"root_count": len(graph), "profiles": sorted(profiles),
            "predecessor_square_completions": descent_squares}


def odd_return(graph, cover, root):
    start, end = (root, 0), (root, 1)
    distances, parents = breadth(cover, start)
    if end not in distances:
        return None
    path = [end]
    while path[-1] != start:
        path.append(parents[path[-1]])
    walk = [v for v, _ in reversed(path)]
    need(walk[0] == walk[-1] and (len(walk)-1) % 2 == 1
         and all(y in graph[x] for x, y in pairwise(walk)), "not an actual odd return")
    return {"length": distances[end], "base_walk": walk}


def audit_rectagraph(graph) -> dict[str, object]:
    local = local_conditions(graph)
    n = len(graph)
    need(local["triangle_free"] and local["unique_other_two_edge_route"] and local["component_sizes"] == [n],
         "expected a connected rectagraph")
    k = audit_regular_from_squares(graph)
    shells = audit_shells(graph, k)
    cover = double_cover(graph)
    cover_local = local_conditions(cover)
    need(cover_local["triangle_free"] and cover_local["unique_other_two_edge_route"], "cover lost local law")
    need(all(len(cover[u, s]) == k for u, s in cover), "cover changed degree")
    expected_cover_routes = {1: 2*n*comb(k, 2)} if k >= 2 else {}
    need(cover_local["other_route_count_histogram"] == expected_cover_routes, "cover did not duplicate local path census")
    connected = cover_local["component_sizes"] == [2*n]
    odd = odd_return(graph, cover, next(iter(graph)))
    need(connected == (odd is not None), "cover connectivity and odd return diverged")
    cover_shells = audit_shells(cover, k)
    if connected:
        need(2*n <= 2**k and n >= 1+k+comb(k, 2), "nonbipartite order bounds")
    else:
        need(cover_local["component_sizes"] == [n, n], "bipartite cover did not split in two")
    return {"vertices": n, "degree": k, "shells": shells, "cover_connected": connected,
            "cover_component_sizes": cover_local["component_sizes"], "cover_shells": cover_shells,
            "odd_return": odd,
            "nonneighbor_without_two_edge_route": sum(v not in ns and v != u and not (ns & graph[v])
                                                        for u, ns in graph.items() for v in graph) // 2}


def forced_minimum_and_unsigned_pairs(graph) -> dict[str, object]:
    root = next(iter(graph))
    ports = tuple(graph[root])
    chart = {root: frozenset()} | {v: frozenset({v}) for v in ports}
    for v in graph.keys() - chart.keys():
        chart[v] = graph[root] & graph[v]
        need(len(chart[v]) == 2, "promoted graph is not diameter two")
    inverse = {p: v for v, p in chart.items()}
    pairs = {frozenset(pair) for pair in combinations(ports, 2)}
    need(len(chart) == len(inverse) == 16 and pairs <= inverse.keys(), "ambiguous pair coordinates")
    for v, occ in chart.items():
        if not occ:
            expected = {inverse[frozenset({w})] for w in ports}
        elif len(occ) == 1:
            expected = {root, *(inverse[p] for p in pairs if occ <= p)}
        else:
            expected = {*occ, *(inverse[p] for p in pairs if not occ & p)}
        need(graph[v] == expected, "root, singleton, and disjoint-pair adjacency differs")
    chosen = frozenset(ports[:2])
    orbit = set()
    for perm in permutations(ports):
        images = dict(zip(ports, perm, strict=True))
        move = {v: inverse[frozenset(images[w] for w in occ)] for v, occ in chart.items()}
        need(all({move[w] for w in graph[v]} == graph[move[v]] for v in graph),
             "rooted coordinate permutation not an automorphism")
        orbit.add(frozenset(images[w] for w in chosen))
    need(orbit == pairs, "an unmarked pair unexpectedly survived all permutations")
    return {"diameter": 2, "root_port_permutations": 120, "unsigned_root_pair_orbit": len(orbit),
            "marked_pair_inferred_from_unmarked_law": False}


def contrast_local_record_and_vertex_return(folded, unfolded) -> dict[str, object]:
    fold_path, cube_path = [0], [0]
    mask = (1 << 5) - 1
    for i in range(5):
        moved = fold_path[-1] ^ (1 << i)
        fold_path.append(min(moved, moved ^ mask))
        cube_path.append(cube_path[-1] ^ (1 << i))
    records = []
    for graph, path in ((folded, fold_path), (unfolded, cube_path)):
        need(all(b in graph[a] for a, b in pairwise(path)), "probe took a non-edge step")
        # A deliberately unsigned record of only degree and two-hop
        # local reunion counts; global vertex equality is a separate input.
        records.append([(len(graph[v]), sorted(len(graph[a] & graph[b])-1
                                               for a, b in combinations(graph[v], 2))) for v in path])
    need(records[0] == records[1] and fold_path[-1] == 0 and cube_path[-1] == mask,
         "local record alias or actual return disappeared")
    return {"same_unsigned_local_record": True, "hops": 5,
            "folded_path": fold_path, "cube_path": cube_path,
            "folded_actual_return": True, "cube_actual_return": False}


def probe() -> dict[str, object]:
    minimum, unfolded, edge = folded_cube(5), cube(5), cube(1)
    larger = cartesian(minimum, edge)
    larger_same_degree = cartesian(minimum, cube(2))
    controls = {
        "one_edge": audit_rectagraph(edge),
        "folded_five": audit_rectagraph(minimum),
        "q5_bipartite_control": audit_rectagraph(unfolded),
        "folded_five_cartesian_k2": audit_rectagraph(larger),
        "folded_five_cartesian_q2": audit_rectagraph(larger_same_degree),
        "folded_seven": audit_rectagraph(folded_cube(7)),
    }
    need(controls["folded_five"]["vertices"] == 16 and controls["folded_five"]["degree"] == 5,
         "minimum fixture changed")
    need(controls["q5_bipartite_control"]["cover_connected"] is False, "Q5 is not a bipartite countercontrol")
    for name, degree, odd in (("folded_five", 5, 5), ("folded_five_cartesian_k2", 6, 5),
                              ("folded_five_cartesian_q2", 7, 5), ("folded_seven", 7, 7)):
        row = controls[name]
        need(row["degree"] == degree and row["odd_return"]["length"] == odd, "larger control changed")
        need(row["cover_shells"]["profiles"] == [tuple(comb(degree, i) for i in range(degree+1))],
             "expected binomial cover census")
        if degree > 5:
            need(row["nonneighbor_without_two_edge_route"] > 0, "local law did not separate from global condition")
    failures = {
        "odd_cycle_c5_missing_alternative": local_conditions(cycle(5)),
        "k33_excess_alternatives": local_conditions(undirected(range(6), product(range(3), range(3, 6)))),
        "k4_has_triangles_despite_local_route_count": local_conditions(
            undirected(range(4), combinations(range(4), 2))),
        "literal_graph_join_not_cartesian": local_conditions(graph_join(minimum, edge)),
    }
    need(failures["odd_cycle_c5_missing_alternative"]["triangle_free"]
         and failures["odd_cycle_c5_missing_alternative"]["other_route_count_histogram"] == {0: 5},
         "missing completion control changed")
    need(failures["k33_excess_alternatives"]["triangle_free"]
         and failures["k33_excess_alternatives"]["other_route_count_histogram"] == {2: 18},
         "excess completion control changed")
    need(failures["k4_has_triangles_despite_local_route_count"]["unique_other_two_edge_route"]
         and not failures["k4_has_triangles_despite_local_route_count"]["triangle_free"],
         "triangle-free assumption not isolated")
    need(not failures["literal_graph_join_not_cartesian"]["triangle_free"], "literal join looked Cartesian")
    band = [{"degree": k, "first_shells_lower_bound": 1+k+comb(k, 2), "odd_cover_upper_bound": 2**(k-1)}
            for k in range(1, 8)]
    need(all(row["first_shells_lower_bound"] > row["odd_cover_upper_bound"] for row in band[:4])
         and band[4]["first_shells_lower_bound"] == band[4]["odd_cover_upper_bound"] == 16,
         "degree threshold arithmetic changed")
    return {"scope": "finite graph conditions and exact controls; no physical or empirical claim",
            "degree_bounds": band, "minimum_structure": forced_minimum_and_unsigned_pairs(minimum),
            "rectagraph_controls": controls, "excluded_controls": failures,
            "odd_return_observation_control": contrast_local_record_and_vertex_return(minimum, unfolded)}


if __name__ == "__main__":
    print(json.dumps(probe(), sort_keys=True, separators=(",", ":")))
