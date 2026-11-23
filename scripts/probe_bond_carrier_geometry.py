"""What carrier did the original two-bond port guard already select?

In a finite simple undirected graph, the degree of a neighbor in the local
four-vertex link counts its common neighbors with the center. Degrees 1,1,2,2
force P4: a disconnected link without isolates would be two disjoint edges;
a connected four-vertex graph with three edges and maximum degree two is a
path. Its ends are nonadjacent: no triangle can have two long edges. Each
long edge has a common neighbor, so spans two short steps. The spanning short
graph is 2-regular; long edges do not join different short components. Thus
on a nonempty connected carrier the short graph is a cycle, and the two long
neighbors exhaust the two distance-two neighbors. Orders below five lack
four distinct neighbors; the squares at five and six fail the codegrees;
all n >= 7 give the required link. Disconnected unions and the empty graph
can pass the original local guard. This argument is not a Lean theorem.

Two explicitly supplied extensions agree on a single line. One preserves
triangle lines at junctions; the other permits all same-type alternatives
at the pivot. Neither selects a spatial dimension or reconstructs a metric.
Run: python3 -m scripts.probe_bond_carrier_geometry
"""

from __future__ import annotations

import json
from collections import Counter
from dataclasses import dataclass
from functools import partial
from itertools import combinations, pairwise, product

if __package__:
    from .probe_conserved_bond_gait import (
        Graph,
        Link,
        Marks,
        Move,
        Ports,
        Vertex,
        link,
        need,
        offers,
    )
else:
    from probe_conserved_bond_gait import (
        Graph,
        Link,
        Marks,
        Move,
        Ports,
        Vertex,
        link,
        need,
        offers,
    )


def simple(graph: Graph) -> None:
    if any(v in ns or any(w not in graph or v not in graph[w] for w in ns)
           for v, ns in graph.items()):
        raise ValueError("requires simple undirected incidence")


def closure(start, neighbors):
    reached, stack = {start}, [start]
    while stack:
        for w in neighbors(stack.pop()):
            if w not in reached:
                reached.add(w)
                stack.append(w)
    return frozenset(reached)


def is_port_link(star: Graph) -> bool:
    simple(star)
    return sorted(map(len, star.values())) == [1, 1, 2, 2]


def link_census() -> dict:
    pairs = list(combinations(range(4), 2))
    accepted = 0
    for mask in range(64):
        graph = {v: set() for v in range(4)}
        for i, (a, b) in enumerate(pairs):
            if mask >> i & 1:
                graph[a].add(b)
                graph[b].add(a)
        if is_port_link(graph):
            ends = [v for v in graph if len(graph[v]) == 1]
            need(ends[1] not in graph[ends[0]] and len(closure(0, graph.__getitem__)) == 4,
                 "accepted non-path neighbor link")
            accepted += 1
    need(accepted == 12, "labeled P4 count changed")
    return {"labeled_neighbor_graphs": 64, "accepted_paths": accepted}


def recover_short_cycle(graph: Graph) -> frozenset[Link]:
    """Verify an unoriented spanning cycle and equality with its square."""
    simple(graph)
    if not graph:
        raise ValueError("connected certificate requires nonempty carrier")
    short = {v: frozenset(w for w in ns if len(ns & graph[w]) == 2) for v, ns in graph.items()}
    for v, ns in graph.items():
        if not is_port_link({w: ns & graph[w] for w in ns}):
            raise ValueError("not an original four-neighbor port link")
        a, b = short[v]
        if ns != (short[v] | short[a] | short[b]) - {v}:
            raise ValueError("short graph square does not reconstruct incidence")
    if len(graph) < 7 or len(closure(next(iter(graph)), short.__getitem__)) != len(graph):
        raise ValueError("requires one connected short cycle of order at least seven")
    return frozenset(link(v, w) for v, ns in short.items() for w in ns)


def local_groups(graph: Graph, v: Vertex) -> frozenset[frozenset[Vertex]]:
    """Same-line incident directions at v: induced-star paths of at most 3 hops."""
    ns = graph[v]
    left, groups = set(ns), set()
    while left:
        group = closure(next(iter(left)), lambda w: graph[w] & ns)
        if not is_port_link({w: graph[w] & group for w in group}):
            raise ValueError("neighborhood is not a union of P4 links")
        groups.add(group)
        left.difference_update(group)
    return frozenset(groups)


@dataclass(frozen=True)
class Line:
    edges: frozenset[Link]
    vertices: frozenset[Vertex]
    short: frozenset[Link]


@dataclass(frozen=True)
class Atlas:
    lines: tuple[Line, ...]
    ports: Ports

    def offers(self, state: Marks) -> frozenset[Move]:
        return offers(self.ports, state)


def compile_lines(graph: Graph) -> Atlas:
    """Global certificate, NOT a locally obtained coordinate or line name."""
    simple(graph)
    if not graph or len(closure(next(iter(graph)), graph.__getitem__)) != len(graph):
        raise ValueError("requires a connected nonempty fixture")
    remaining = {link(v, w) for v, ns in graph.items() for w in ns}
    if not remaining:
        raise ValueError("no carrier edges")

    def adjacent_edges(edge):
        a, b = edge
        for c in graph[a] & graph[b]:
            yield link(a, c)
            yield link(b, c)

    lines, short, motifs = [], set(), {}
    incident = {v: set() for v in graph}
    while remaining:
        edges = closure(next(iter(remaining)), adjacent_edges)
        remaining.difference_update(edges)
        sub = {}
        for a, b in edges:
            sub.setdefault(a, set()).add(b)
            sub.setdefault(b, set()).add(a)
        cert = recover_short_cycle(sub)
        ports = Ports.from_graph(sub)
        need(cert == ports.short_links, "line reconstruction disagrees with original guard")
        lines.append(Line(edges, frozenset(sub), cert))
        short.update(cert)
        motifs.update(ports.motifs)
        for v, ns in sub.items():
            incident[v].add(frozenset(ns))
    for v, groups in incident.items():
        need(groups == local_groups(graph, v), "global partition disagrees with bounded star")
    return Atlas(tuple(lines), Ports(frozenset(short), motifs))


class FreeAlternatives:
    """Alternative lift: same partner, pivot and occupancy rules, all destinations.

    For comparison on the same certified fixtures. This kernel uses ambient
    codegrees, not compiled line membership, positions or relabeling order.
    """
    def __init__(self, graph: Graph):
        simple(graph)
        self.graph = graph
        self.short = {v: {w for w in ns if len(ns & graph[w]) == 2} for v, ns in graph.items()}
        self.long = {v: {w for w in ns if len(ns & graph[w]) == 1} for v, ns in graph.items()}
        if any(self.short[v] | self.long[v] != ns for v, ns in graph.items()):
            raise ValueError("edge does not have original short or long codegree")
        self.shorts = {link(v, w) for v in graph for w in self.short[v]}
        self.longs = {link(v, w) for v in graph for w in self.long[v]}

    def offers(self, state: Marks) -> frozenset[Move]:
        moves = set()
        for bond in self.longs & state:
            a, b = bond
            midpoint, = self.graph[a] & self.graph[b]
            for s in self.shorts & state:
                shared = bond & s
                if shared:
                    z, = shared
                    t, = s - {z}
                    pivot = z if t == midpoint else t
                    old, dests = s, self.short[pivot] - s
                else:
                    near = [v for v in bond if self.short[v] & s]
                    if len(near) != 1:
                        continue
                    pivot, = near
                    old, dests = bond, self.long[pivot] - bond
                for dest in dests:
                    new = link(pivot, dest)
                    if new not in state:
                        moves.add(Move(pivot, old, new))
        return frozenset(moves)


# Only the fixture/oracle layer below uses indices, lengths and named axes.
def labeled_regular_graphs(n: int):
    """Complete upper-triangle row choices; no quotient by isomorphism."""
    graph = {v: set() for v in range(n)}

    def fill(v):
        if v == n:
            yield {w: frozenset(ns) for w, ns in graph.items()}
            return
        eligible = [w for w in range(v+1, n) if len(graph[w]) < 4]
        for targets in combinations(eligible, 4-len(graph[v])):
            graph[v].update(targets)
            for w in targets:
                graph[w].add(v)
            yield from fill(v+1)
            for w in targets:
                graph[w].remove(v)
            graph[v].difference_update(targets)
    yield from fill(0)


def small_regular_census() -> dict:
    rows = {}
    for n in (5, 6, 7):
        total = accepted = 0
        for graph in labeled_regular_graphs(n):
            total += 1
            try:
                ports = Ports.from_graph(graph)
            except ValueError:
                continue
            need(ports.short_links == recover_short_cycle(graph), "census reconstruction failed")
            accepted += 1
        rows[n] = {"labeled": total, "accepted": accepted}
    return rows


def product_graph(sizes: tuple[int, ...]) -> Graph:
    if not sizes or min(sizes) < 7:
        raise ValueError("fixture requires cycle squares of order >= 7")
    return {v: frozenset(v[:i] + ((v[i] + d) % n,) + v[i+1:]
                         for i, n in enumerate(sizes) for d in (-2, -1, 1, 2))
            for v in product(*(range(n) for n in sizes))}


def wedge_point(axis, i, n):
    return (axis, i % n) if i % n else (0, 0)


def wedge_graph(n: int, m: int) -> Graph:
    if min(n, m) < 7:
        raise ValueError("fixture requires cycle squares of order >= 7")
    graph = {}
    for axis, size in enumerate((n, m)):
        for i in range(size):
            ns = graph.setdefault(wedge_point(axis, i, size), set())
            ns.update(wedge_point(axis, i+d, size) for d in (-2, -1, 1, 2))
    return {v: frozenset(ns) for v, ns in graph.items()}


def orbit(rule, start):
    return closure(start, lambda s: (m.apply(s) for m in rule.offers(s)))


def crossing_seed(point):
    return frozenset((link(point(-3), point(-1)), link(point(-1), point(0))))


def fixture_result(name, graph, axes):
    atlas = compile_lines(graph)
    try:
        Ports.from_graph(graph)
    except ValueError:
        old_accepts = False
    else:
        old_accepts = True
    seeds = [crossing_seed(axis) for axis in axes[:2]]
    first = seeds[0]
    initial_line, = [line for line in atlas.lines if first <= line.edges]
    single = orbit(atlas, first)
    need(all(s <= initial_line.edges and len(atlas.offers(s)) == 1 for s in single),
         "single seed stalled, branched or left its line")
    row = {"name": name, "old_guard_accepts": old_accepts,
           "line_length_histogram": dict(sorted(Counter(len(line.vertices) for line in atlas.lines).items())),
           "lines_at_vertex_histogram": dict(Counter(len(local_groups(graph, v)) for v in graph)),
           "single_states": len(single)}
    if len(seeds) == 2:
        second = seeds[1]
        second_line, = [line for line in atlas.lines if second <= line.edges]
        target = axes[1](1)
        need(target not in initial_line.vertices, "target is not transverse")
        hit = any(any(target in e for e in s) for s in single)
        need(not hit, "single seed reaches the transverse target")
        other = orbit(atlas, second)
        joint = orbit(atlas, first | second)
        need(joint == {a | b for a in single for b in other}, "reachable set is not the product")
        same = 0
        for s in joint:
            actual = atlas.offers(s)
            need(len(actual) == 2 and actual == atlas.offers(s & initial_line.edges) |
                 atlas.offers(s & second_line.edges), "cross-line interference")
            same += len({m.center for m in actual}) == 1
        row.update(transverse_target_reached=hit, joint_states=len(joint), joint_same_center_states=same)
    return row


def junction_control() -> dict:
    sizes = (11, 13)
    graph = wedge_graph(*sizes)
    atlas, free = compile_lines(graph), FreeAlternatives(graph)

    def a(i):
        return wedge_point(0, i, sizes[0])

    def b(i):
        return wedge_point(1, i, sizes[1])

    j = a(0)
    path = [frozenset((e, s)) for e, s in (
        (link(a(-2), j), link(a(-1), j)), (link(a(-2), j), link(j, b(1))),
        (link(a(-2), j), link(b(1), b(2))), (link(j, b(2)), link(b(1), b(2))),
        (link(j, b(2)), link(b(2), b(3))))]
    for s, t in pairwise(path):
        need(t in {m.apply(s) for m in free.offers(s)}, "missing free-alternative transfer")
    states = orbit(free, path[0])
    jam = [frozenset((e, s)) for e, s in (
        (link(a(-3), a(-1)), link(a(-1), j)), (link(a(-3), a(-1)), link(j, b(-1))),
        (link(a(-1), a(1)), link(j, b(-1))))]
    need(jam[0] in states, "jam witness is not reachable from the original seed")
    for s, t in pairwise(jam):
        need(t in {m.apply(s) for m in free.offers(s)}, "missing jam path")
    need(not free.offers(jam[-1]), "supposed jam has an exit")
    retained = orbit(atlas, path[0])
    line, = [line for line in atlas.lines if path[0] <= line.edges]
    need(all(s <= line.edges for s in retained), "line-preserving lift turned")
    orientations = []
    for n, p in zip(sizes, (a, b)):
        starts = {frozenset((link(p(i), p(i+2*h)), link(p(i+2*h), p(i+3*h))))
                  for i in range(n) for h in (-1, 1)}
        need(len(starts) == 2*n and starts <= states, "some oriented phase-A states unreachable")
        orientations.append(len(starts))
    return {"wedge_sizes": sizes, "offers_along_witness": [len(free.offers(s)) for s in path],
            "offers_along_jam_witness": [len(free.offers(s)) for s in jam],
            "reachable_outdegrees": dict(sorted(Counter(len(free.offers(s)) for s in states).items())),
            "free_reachable_states": len(states), "same_line_reachable_states": len(retained),
            "same_line_reaches_other_ring": path[-1] in retained,
            "all_phase_a_orientations_positions": orientations}


def report() -> dict:
    rows = []
    def axis(i, *, ns, d):
        return tuple(i % n if j == d else 0 for j, n in enumerate(ns))
    for ns in ((7,), (7, 8), (7, 7, 7)):
        axes = [partial(axis, ns=ns, d=d) for d in range(len(ns))]
        rows.append(fixture_result("product_" + "x".join(map(str, ns)), product_graph(ns), axes))
    rows.append(fixture_result("wedge_7_8", wedge_graph(7, 8),
                               [lambda i: wedge_point(0, i, 7), lambda i: wedge_point(1, i, 8)]))
    return {"neighbor_links": link_census(), "small_regular_census": small_regular_census(),
            "fixtures": rows, "alternative_lift": junction_control(),
            "boundary": "Connected original carriers are cycle squares. Products and a point-gluing "
                        "are supplied controls. Triangle-line compilation is global; a crossing "
                        "star distinguishes incident directions locally. Staying or turning at a "
                        "junction depends on the supplied lift. No dimension selection, signal "
                        "geometry, manifold, scheduler, or physical claim follows."}


if __name__ == "__main__":
    print(json.dumps(report(), indent=2))
