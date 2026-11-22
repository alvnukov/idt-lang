"""An aggregate pair-contact rate does not certify unique local reunions.

Exhaust N=k(k-1) non-backtracking two-hop words available at one regular
root. If c_y words reach the same endpoint, independent uniform words
give P2=sum(c_y²)/N² and P3=sum(c_y³)/N³. Then

  N²*P3 - 4*N*P2 + 4 = sum_y c_y (c_y-2)² / N.

This is nonnegative and zero exactly when every used endpoint has two
words. It upper-bounds the fraction of words ending at offending y.
This tests one root, not unreachable vertices or global oddness.
If all indexed pair comparisons are retained, they determine the
equality partition already; the negative result concerns the aggregate
pair moment alone, not that richer record.

Operational premises: the apparatus is restored between trials; local
ports and the immediate reverse port can be distinguished for each word;
three tokens/records can meet at a common two-hop time and certify true
endpoint equality without changing paths or dropping misses. Alternatively
one may use a reliable local arrival register with a fixed timing window.
Equal elapsed hop count or equal local labels alone do not certify
identity. Independent uniform words (with replacement), or explicitly
uniform distinct words, are one sampling protocol; deterministic exhaustive
comparison needs no sampling premise. Incomplete trials do not get a
zero-defect claim here. The fixtures expose an ideal contact comparator;
they are not a demonstration of its implementation.

For the weaker rule "at least one alternate", a shortest odd cycle C_m
in a triangle-free graph is induced. Each consecutive triple of C_m
needs an exterior witness. An exterior vertex adjacent to two cycle
vertices makes an odd cycle by adding its two edges to the odd arc.
That arc must have length at least m-2, so the other (even) arc has
length exactly two. The step-two graph of odd C_m (m>=5) is itself a
triangle-free cycle; no exterior vertex has three cycle neighbours.
Therefore the m witnesses are different and the graph has >=2m>=10
vertices. C5[2] achieves ten; it does not satisfy the stronger law.
"""

from __future__ import annotations

import json
from collections import Counter, deque
from collections.abc import Callable
from fractions import Fraction
from itertools import combinations, permutations
from math import comb

Graph = dict[int, frozenset[int]]


def need(condition, why):
    if not condition:
        raise ArithmeticError(why)


def undirected(size: int, edges) -> Graph:
    graph: dict[int, set[int]] = {u: set() for u in range(size)}
    for u, v in edges:
        graph[u].add(v)
        graph[v].add(u)
    return {u: frozenset(ns) for u, ns in graph.items()}


def edge_set(graph: Graph) -> set[tuple[int, int]]:
    return {(u, v) for u, ns in graph.items() for v in ns if u < v}


def folded_five() -> Graph:
    return {v: frozenset(min(v ^ (1 << i), v ^ (1 << i) ^ 31) for i in range(5)) for v in range(16)}


def cube_five() -> Graph:
    return {v: frozenset(v ^ (1 << i) for i in range(5)) for v in range(32)}


def c5_twins() -> Graph:
    return {u: frozenset(2*((u//2 + direction) % 5) + j for direction in (-1, 1) for j in (0, 1))
            for u in range(10)}


def cartesian_edge(graph: Graph) -> Graph:
    return {2*u+s: frozenset({2*v+s for v in ns} | {2*u+1-s})
            for u, ns in graph.items() for s in (0, 1)}


def pair_only_decoy() -> tuple[Graph, Graph]:
    # At the root, all ten unordered port pairs are initially represented
    # by endpoint nodes. Replace the three pairs within the port triangle
    # {1,2,3} by one triple endpoint and one singleton at each port.
    groups = [(1, 2, 3), (1,), (2,), (3,)]
    groups.extend(pair for pair in combinations(range(1, 6), 2) if not set(pair) <= {1, 2, 3})
    graph_edges = {(0, p) for p in range(1, 6)}
    for index, ports in enumerate(groups, 6):
        graph_edges.update((p, index) for p in ports)
    local = undirected(17, graph_edges)
    need(len(groups) == 11 and all(len(local[x]) == 5 for x in range(6)), "wrong controlled neighbourhood")
    # Complete to a 5-regular bipartite graph without moving the first
    # two shells. Seven new right-side nodes fill all 35 left deficits;
    # each endpoint sees distinct new nodes and cyclic allocation balances.
    position = 0
    for endpoint in range(6, 17):
        for _ in range(5-len(local[endpoint])):
            graph_edges.add((endpoint, 17+position % 7))
            position += 1
    full = undirected(24, graph_edges)
    need(position == 35 and all(len(ns) == 5 for ns in full.values()), "degree completion failed")
    return local, full


def nonbipartite_completion(bipartite: Graph, folded: Graph) -> Graph:
    # Reciprocal two-switch after disjoint union. No first-port edge or
    # two-hop endpoint from root 0 is moved. The two cross-edges have
    # disjoint endpoints, so cannot introduce a triangle.
    a, b = min((x, y) for x, y in edge_set(bipartite) if x >= 6 and y >= 17)
    c, d = min(edge_set(folded))
    offset = len(bipartite)
    edges = edge_set(bipartite) | {(u+offset, v+offset) for u, v in edge_set(folded)}
    edges.difference_update(((a, b), (c+offset, d+offset)))
    edges.update(((a, c+offset), (b, d+offset)))
    return undirected(offset+len(folded), edges)


def cayley_s4_counter() -> Graph:
    # A selected finite-search control, not a primitive. All five
    # generators are involutions; left translations preserve rooted
    # path-contact statistics at every vertex.
    vertices = tuple(permutations(range(4)))
    index = {p: i for i, p in enumerate(vertices)}
    generators = ((0, 1, 3, 2), (0, 2, 1, 3), (0, 3, 2, 1), (1, 0, 2, 3), (2, 3, 0, 1))
    return {i: frozenset(index[tuple(p[u] for u in g)] for g in generators) for i, p in enumerate(vertices)}


def bfs(graph) -> tuple[set[int], dict[int, int]]:
    root = min(graph)
    colors, queue = {root: 0}, deque([root])
    while queue:
        u = queue.popleft()
        for v in graph[u]:
            if v not in colors:
                colors[v] = 1-colors[u]
                queue.append(v)
    return set(colors), colors


def shortest_odd_cycle(graph: Graph) -> list[int] | None:
    reachable, color = bfs(graph)
    need(reachable == set(graph), "fixture not connected")
    if all(color[u] != color[v] for u, v in edge_set(graph)):
        return None
    best = None
    for u in graph:
        first, goal = (u, 0), (u, 1)
        parent = {first: None}
        todo = deque([first])
        while todo and goal not in parent:
            v, bit = todo.popleft()
            for w in sorted(graph[v]):
                state = w, 1-bit
                if state not in parent:
                    parent[state] = (v, bit)
                    todo.append(state)
        need(goal in parent, "nonbipartite fixture lacks actual odd return")
        path = []
        cursor = goal
        while cursor is not None:
            path.append(cursor[0])
            cursor = parent[cursor]
        path.reverse()
        if best is None or len(best) > len(path):
            best = path
    need(best is not None and len(best) % 2 == 0 and best[0] == best[-1]
         and len(set(best[:-1])) == len(best)-1, "shortest odd return not a simple odd cycle")
    return best


def two_hop_endpoints(graph: Graph, root: int) -> tuple[int, ...]:
    return tuple(v for x in sorted(graph[root]) for v in sorted(graph[x] - {root}))


def fixture_contact(endpoints: tuple[int, ...]) -> Callable[[tuple[int, ...]], bool]:
    # Only the fixture knows the simulated endpoint IDs; the moment
    # observer receives the Boolean equality of specified word indices.
    def contact(indices):
        return len({endpoints[i] for i in indices}) == 1

    return contact


def contact_moments(word_count: int, contact: Callable[[tuple[int, ...]], bool],
                    budget: int | None = None) -> dict[str, object]:
    n = word_count
    need(n > 0, "no operational two-hop attempts")
    planned, used = comb(n, 2) + comb(n, 3), 0
    distinct_contacts = []
    for r in (2, 3):
        clicks = 0
        for indices in combinations(range(n), r):
            if budget is not None and used >= budget:
                return {"completion": "incomplete", "checked_contacts": used,
                        "planned_contacts": planned, "conclusion": None}
            clicks += contact(indices)
            used += 1
        distinct_contacts.append(clicks)
    f2, f3 = 2*distinct_contacts[0], 6*distinct_contacts[1]
    m2, m3 = n+f2, n+3*f2+f3
    defect = Fraction(m3-4*m2+4*n, n)
    need(defect == Fraction(f3-f2+n, n) >= 0, "nonnegative moment defect")
    return {"completion": "exhaustive", "checked_contacts": used, "planned_contacts": planned,
            "N": n, "sum_c_squared": m2, "sum_c_cubed": m3,
            "pair_probability_with_replacement": str(Fraction(m2, n**2)),
            "triple_probability_with_replacement": str(Fraction(m3, n**3)),
            "ordered_distinct_pair_contacts": f2, "ordered_distinct_triple_contacts": f3,
            "ordered_distinct_pair_contact_probability": str(Fraction(f2, n*(n-1))) if n > 1 else None,
            "ordered_distinct_triple_contact_probability": str(Fraction(f3, n*(n-1)*(n-2))) if n > 2 else None,
            "offending_word_fraction_upper_bound": str(min(Fraction(1), defect)),
            "defect": str(defect), "unique_other_path_at_this_root": defect == 0}


def local_report(graph: Graph, root: int) -> dict[str, object]:
    endpoints = two_hop_endpoints(graph, root)
    k = len(graph[root])
    need(all(len(graph[v]) == k for v in graph[root]) and len(endpoints) == k*(k-1),
         "root/port degree or word inventory changed")
    measured = contact_moments(len(endpoints), fixture_contact(endpoints))
    counts = Counter(endpoints)
    n = measured["N"]
    direct = Fraction(sum(c*(c-2)**2 for c in counts.values()), n)
    bad_fraction = Fraction(sum(c for c in counts.values() if c != 2), n)
    need(int(measured["sum_c_squared"]) == sum(c**2 for c in counts.values())
         and int(measured["sum_c_cubed"]) == sum(c**3 for c in counts.values())
         and Fraction(measured["defect"]) == direct >= bad_fraction,
         "equality-only reconstruction differs from independent fixture count")
    return {"degree": k, "endpoint_histogram": dict(sorted(Counter(counts.values()).items())),
            "exact_bad_fraction_from_fixture": str(bad_fraction), **measured}


def graph_report(graph: Graph) -> dict[str, object]:
    need(all(u not in row and all(u in graph[v] for v in row) for u, row in graph.items()),
         "not reciprocal simple graph")
    need(all(not graph[u] & graph[v] for u, v in edge_set(graph)), "not triangle-free")
    odd = shortest_odd_cycle(graph)
    reference = local_report(graph, min(graph))
    signatures = Counter()
    for u in graph:
        row = local_report(graph, u)
        signatures[row["sum_c_squared"], row["sum_c_cubed"], row["defect"]] += 1
    weak = all(min(Counter(two_hop_endpoints(graph, u)).values()) >= 2 for u in graph)
    return {"vertices": len(graph), "degrees": sorted({len(ns) for ns in graph.values()}),
            "genuine_odd_cycle_length": None if odd is None else len(odd)-1,
            "genuine_odd_cycle_witness": odd, "weak_law_all_roots": weak,
            "root": reference, "all_root_moment_signatures": [
                {"sum_c_squared": a, "sum_c_cubed": b, "defect": d, "roots": count}
                for (a, b, d), count in sorted(signatures.items())]}


def weak_minimum_witness(graph: Graph) -> dict[str, object]:
    walk = shortest_odd_cycle(graph)
    need(walk is not None, "weak minimum has no odd witness")
    cycle = walk[:-1]
    outside = set(graph) - set(cycle)
    witnesses = []
    for i, u in enumerate(cycle):
        before, after = cycle[i-1], cycle[(i+1) % len(cycle)]
        alternates = graph[before] & graph[after] & outside
        need(not (graph[before] & graph[after] & set(cycle)) - {u}
             and len(alternates) == 1, "not the sharp exterior witness fixture")
        witnesses.append(next(iter(alternates)))
    need(len(set(witnesses)) == len(cycle) and set(witnesses) == outside, "sharp lower-order fixture")
    return {"shortest_odd_cycle": walk, "distinct_exterior_alternates_in_cycle_order": witnesses,
            "attained_lower_bound": 2*len(cycle)}


def probe() -> dict[str, object]:
    local, paired = pair_only_decoy()
    folded, twins = folded_five(), c5_twins()
    loose = cartesian_edge(twins)
    groups = {"folded_five": graph_report(folded), "cube_five_bipartite": graph_report(cube_five()),
              "required_histogram_regular_bipartite_completion": graph_report(paired),
              "required_histogram_regular_nonbipartite_switch": graph_report(nonbipartite_completion(paired, folded)),
              "s4_all_roots_pair_only_impostor": graph_report(cayley_s4_counter()),
              "c5_twins_weak_minimum": graph_report(twins), "c5_twins_cartesian_k2": graph_report(loose)}
    for key, (m2, m3, defect, oddness) in {
        "folded_five": (40, 80, "0", True), "cube_five_bipartite": (40, 80, "0", False),
        "required_histogram_regular_bipartite_completion": (40, 86, "3/10", False),
        "required_histogram_regular_nonbipartite_switch": (40, 86, "3/10", True),
        "s4_all_roots_pair_only_impostor": (40, 92, "3/5", True),
        "c5_twins_weak_minimum": (32, 96, "4/3", True), "c5_twins_cartesian_k2": (48, 128, "4/5", True),
    }.items():
        row = groups[key]
        counts = row["root"]
        need((counts["sum_c_squared"], counts["sum_c_cubed"], counts["defect"],
              row["genuine_odd_cycle_length"] is not None) == (m2, m3, defect, oddness), "fixture outcome changed")
    pure_local = local_report(local, 0)
    need(pure_local["endpoint_histogram"] == {1: 3, 2: 7, 3: 1}
         and pure_local == groups["required_histogram_regular_bipartite_completion"]["root"]
         and pure_local == groups["required_histogram_regular_nonbipartite_switch"]["root"],
         "local statistic changed under completion")
    signatures = groups["s4_all_roots_pair_only_impostor"]["all_root_moment_signatures"]
    need(signatures == [{"sum_c_squared": 40, "sum_c_cubed": 92, "defect": "3/5", "roots": 24}],
         "pair-only counterexample depends on viewing root")
    need(groups["c5_twins_weak_minimum"]["weak_law_all_roots"]
         and groups["c5_twins_cartesian_k2"]["weak_law_all_roots"], "weak law failed")
    attempted = two_hop_endpoints(local, 0)
    truncated = contact_moments(len(attempted), fixture_contact(attempted), budget=1300)
    need(truncated == {"completion": "incomplete", "checked_contacts": 1300,
                       "planned_contacts": 1330, "conclusion": None}, "truncated contacts produced a conclusion")
    return {"scope": "ideal finite contact counters only; no physical detector or statistical claim",
            "pure_local_fixture": {"local_vertices": len(local), "global_oddness_from_radius_two": "unknown",
                                   "root": pure_local},
            "graph_controls": groups, "weak_minimum": weak_minimum_witness(twins),
            "incomplete_contact_control": truncated}


if __name__ == "__main__":
    print(json.dumps(probe(), sort_keys=True, separators=(",", ":")))
