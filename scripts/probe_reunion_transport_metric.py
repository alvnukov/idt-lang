"""Conditional transport on the free abelian return cover of folded five.

The folded construction supplies the input adjacency only. Squares,
tree chords and period charts below are recovered from that adjacency
and the declared omitted square relations. A free period is a signed
route-homology record, not a Euclidean position. Distances are shortest
closed route costs under an explicit reciprocal hop clock.

For m selected root edges write P+ and P- for sums of positive and
negative unit-period counts. A simple closed route through the root
uses at most two root edges; its only nonzero periods are ±e_i and
e_i-e_j. Squares realize every such generator. Consequently the
unit-hop return cost is exactly 4*max(P+,P-). Giving each selected
edge one extra mandatory tick changes the cost to 3*||p||_1 +
2*|sum(p)|, without changing the relations or rank. The lower bounds
follow by decomposing a walk into simple cycles and applying these
norms' triangle inequalities; the upper bounds pair opposite counts
and realize the remaining singles.

For an asymptotic comparison, every closed walk decomposes into simple
cycles; conversely finitely many cycles can be repeated in any rational
ratio with bounded connector overhead. The convex velocity body can
therefore be certified from attained square means and exact edge
potentials ruling out a larger mean cycle in each facet direction.

An internal experiment still needs actual root identity, stable local
port recognition, a signed memory updated consistently on reverse
hops, a specified clock and reliable trials/exhaustion to certify a
shortest time. Finite residues alone do not establish an infinite rank.
Nothing here supplies spatial lengths, isotropic directions, dynamical
symmetry, or Lorentz/Euclidean propagation.
"""

from __future__ import annotations

import heapq
import json
from collections import Counter, deque
from fractions import Fraction
from itertools import combinations, pairwise, product
from math import comb, gcd, lcm

Graph = dict[int, frozenset[int]]
Edge = tuple[int, int]
Face = tuple[int, int, int, int]
Vec = tuple[int, ...]
Gains = dict[Edge, Vec]


def need(ok, why):
    if not ok:
        raise ArithmeticError(why)


def fixture() -> Graph:
    return {v: frozenset(min(v ^ (1 << i), v ^ (1 << i) ^ 31) for i in range(5)) for v in range(16)}


def edge(u: int, v: int) -> Edge:
    return min(u, v), max(u, v)


def neg(a):
    return tuple(-x for x in a)


def add(a, b):
    return tuple(x+y for x, y in zip(a, b, strict=True))


def sub(a, b):
    return add(a, neg(b))


def dot(a, b):
    return sum(x*y for x, y in zip(a, b, strict=True))


def cross(a, b):
    return a[1]*b[2]-a[2]*b[1], a[2]*b[0]-a[0]*b[2], a[0]*b[1]-a[1]*b[0]


def determinant(vectors) -> int:
    if len(vectors) == 2:
        a, b = vectors
        return a[0]*b[1]-a[1]*b[0]
    a, b, c = vectors
    return dot(a, cross(b, c))


def coordinates(v, basis, det):
    return tuple(Fraction(determinant((*basis[:i], v, *basis[i+1:])), det) for i in range(len(basis)))


def faces_from_adjacency(graph: Graph) -> tuple[Face, ...]:
    squares = {(u, v, w, z) for u in graph for v in graph[u] if v > u
               for w in graph[v] if w > u
               for z in graph[u] & graph[w] if z > v}
    need(len(squares) == 40, "square inventory")
    return tuple(sorted(squares))


def tree_vertices(graph: Graph, root: int) -> dict[int, int | None]:
    parents = {root: None}
    queue = deque([root])
    while queue:
        u = queue.popleft()
        for v in sorted(graph[u]):
            if v not in parents:
                parents[v] = u
                queue.append(v)
    need(len(parents) == len(graph), "failed to recover connected tree")
    return parents


def ordered_gain(gains: Gains) -> Gains:
    return {**gains, **{(v, u): neg(w) for (u, v), w in gains.items()}}


def nullspace(rows, width: int):
    echelon = {}
    for source in rows:
        row = list(map(Fraction, source))
        for i in range(width):
            if not row[i]:
                continue
            a = row[i]
            if i not in echelon:
                echelon[i] = [x/a for x in row]
                break
            row = [x-a*y for x, y in zip(row, echelon[i], strict=True)]
    columns = []
    for free in sorted(set(range(width)) - echelon.keys()):
        modes = [Fraction(int(j == free)) for j in range(width)]
        for i, row in sorted(echelon.items(), reverse=True):
            modes[i] = -sum(row[j]*modes[j] for j in range(i+1, width))
        scale = lcm(*(x.denominator for x in modes))
        columns.append(tuple(int(x*scale) for x in modes))
    return tuple(zip(*columns, strict=True))


def face_word(f: Face) -> tuple[int, ...]:
    return *f, f[0]


def loop_period(word, gains: Gains) -> Vec:
    steps = [gains[u, v] for u, v in pairwise(word)]
    return tuple(map(sum, zip(*steps, strict=True)))


def primitive_chart(graph: Graph, faces: tuple[Face, ...], broken: set[int], root: int) -> tuple[Gains, int]:
    edges = tuple(sorted({edge(u, v) for u in graph for v in graph[u]}))
    parents = tree_vertices(graph, root)
    tree = {edge(u, v) for u, v in parents.items() if v is not None}
    chords = tuple(u for u in edges if u not in tree)
    need(len(chords) == 25, "wrong cycle generator count")

    def relator(f):
        travel = set(pairwise(face_word(f)))
        return tuple(int(uv in travel)-int(uv[::-1] in travel) for uv in chords)

    images = nullspace((relator(f) for i, f in enumerate(faces) if i not in broken), len(chords))
    need(len(images) == len(chords), "missing free period components")
    dimension = len(images[0])
    need(dimension in (2, 3), "expected rank-two/rank-three comparison")
    data = [(abs(determinant(c)), c) for c in combinations(sorted(set(images)), dimension)]
    index = gcd(*(d for d, _ in data))
    witnesses = next((c for d, c in data if d == index), None)
    need(index > 0 and witnesses is not None, "comparison needs an attaining full-rank chord minor")
    # The gcd of full-rank minors is the index of the image lattice in
    # Z^d. An attaining minor supplies an integral basis for this image.
    # Independently require each original chord's new coordinates to be
    # integral and the b_i chord images to occur, verifying primitivity.
    coords = [coordinates(v, witnesses, determinant(witnesses)) for v in images]
    need(all(x.denominator == 1 for row in coords for x in row), "basis not primitive for generated periods")
    chord_gains = dict(zip(chords, (tuple(map(int, row)) for row in coords), strict=True))
    gains = ordered_gain({e: chord_gains.get(e, (0,)*dimension) for e in edges})
    need(all(not any(loop_period(face_word(f), gains)) for i, f in enumerate(faces) if i not in broken),
         "retained square has nonzero period")
    return gains, dimension


def marked_edges(graph: Graph, faces: tuple[Face, ...], r: int, select_complement: bool) -> tuple[set[int], tuple[int, ...]]:
    mark = min(graph.keys()-graph[r]-{r})
    common = graph[r] & graph[mark]
    ports = tuple(sorted(graph[r]-common if select_complement else common))
    broken = {i for i, f in enumerate(faces)
              if any(edge(u, v) == edge(r, p) for u, v in pairwise(face_word(f)) for p in ports)}
    return broken, ports


def mark_metric(graph, faces, root, complement):
    broken, selected = marked_edges(graph, faces, root, complement)
    abstract, d = primitive_chart(graph, faces, broken, root)
    need(d == len(selected), "mark unexpectedly does not induce matching rank")
    gains = {(u, v): tuple(int(u == root and v == p)-int(v == root and u == p) for p in selected)
             for u in graph for v in graph[u]}
    baseline = min(graph[root]-set(selected))
    words = []
    for p in selected:
        mid, = (graph[p] & graph[baseline]) - {root}
        words.append((root, p, mid, baseline, root))
    need(tuple(loop_period(w, gains) for w in words)
         == tuple(tuple(int(i == j) for i in range(d)) for j in range(d)), "marked unit periods")
    frame = tuple(loop_period(w, abstract) for w in words)
    det = determinant(frame)
    need(abs(det) == 1, "marked periods not an integral change of chart")
    offset = {root: (0,)*d}
    for v, u in tree_vertices(graph, root).items():
        if u is not None:
            offset[v] = add(offset[u], gains[u, v])
    need(all(sub(add(offset[u], w), offset[v]) == coordinates(abstract[u, v], frame, det)
             for (u, v), w in gains.items()), "root-local counters do not realize independently recovered quotient")
    return gains, words, selected


def arrival_minima(graph, gains: Gains, r: int, horizon: int | None, *,
                   time=None, modulus=None, keep_parity=False):
    need(horizon is not None or modulus is not None, "arrival search needs a time bound or finite modulus")
    n = len(next(iter(gains.values())))
    initial = (r, (0,)*(n+int(keep_parity)))
    queue = [(0, initial)]
    cost = {initial: 0}
    arrivals = {}
    while queue:
        t, (v, p) = heapq.heappop(queue)
        if t != cost[v, p]:
            continue
        if v == r:
            arrivals[p] = t
        for v2 in graph[v]:
            t2 = t + (time[edge(v, v2)] if time else 1)
            if horizon is not None and t2 > horizon:
                continue
            p2 = add(p[:n], gains[v, v2])
            if modulus:
                p2 = tuple(x % modulus for x in p2)
            if keep_parity:
                p2 += (1-p[-1],)  # actual hop parity, not clock-time parity
            state = v2, p2
            if state not in cost or t2 < cost[state]:
                cost[state] = t2
                heapq.heappush(queue, (t2, state))
    return arrivals


def cost_formula(v: Vec, slow: bool) -> int:
    return (3 if slow else 2)*sum(map(abs, v)) + 2*abs(sum(v))


def counts_at(times, arrivals):
    return [sum(cost <= t for cost in arrivals.values()) for t in times]


def rooted_frontiers(graph: Graph, gains: Gains, selected: tuple[int, ...], root: int) -> dict[str, object]:
    n = len(selected)
    time = {edge(u, v): 1+int(u == root and v in selected or v == root and u in selected) for u, v in gains}
    report = {}
    for slow in (False, True):
        horizon = 16
        found = arrival_minima(graph, gains, root, horizon, time=time if slow else None)
        p_range = range(-horizon//4, horizon//4+1)
        expected = {p: cost_formula(p, slow) for p in product(p_range, repeat=n) if cost_formula(p, slow) <= horizon}
        need(found == expected, "exact rooted cost formula and lifted BFS disagree")
        u, v = (1, 0)+(0,)*(n-2), (0, 1)+(0,)*(n-2)
        a, b, plus, minus = (found[p] for p in (u, v, add(u, v), sub(u, v)))
        delta = plus**2 + minus**2 - 2*(a*a+b*b)
        need(delta != 0, "parallelogram unexpectedly holds")
        report["mandatory_extra_tick_on_selected_edges" if slow else "one_tick_every_edge"] = {
            "return_counts_through_ticks_4_to_16": counts_at(range(4, 17), found),
            "u_v_sum_difference_costs": [a, b, plus, minus], "squared_parallelogram_defect": delta,
        }
    for m in range(5):
        closed_form_count = sum(comb(n, u)*comb(n-u, v)*comb(m, u)*comb(m, v)
                                for u in range(n+1) for v in range(n-u+1))
        observed = report["one_tick_every_edge"]["return_counts_through_ticks_4_to_16"][4*m-4] if m else 1
        need(observed == closed_form_count, "rooted period ball polynomial check")
    return report


def verify_facet(gains: Gains, a, bound, scale) -> None:
    """Find a potential h(v) >= h(u) + scale*a·gain - bound."""
    height = dict.fromkeys({u for u, _ in gains}, 0)
    arcs = tuple((u, v, scale*dot(a, w)-bound) for (u, v), w in gains.items())
    for _ in height:
        upper = dict(height)
        for u, v, e in arcs:
            upper[v] = max(upper[v], height[u]+e)
        if upper == height:
            break
        height = upper
    need(all(height[v] >= height[u]+e for u, v, e in arcs), "long cycle violates proposed velocity facet")


def velocity_body_from_squares(gains: Gains, faces: tuple[Face, ...]) -> dict[str, object]:
    square_vectors = {loop_period(face_word(f), gains) for f in faces}
    square_vectors |= {neg(p) for p in square_vectors}
    affine_vertices = sorted(square_vectors)
    need(any(determinant(c) for c in combinations(affine_vertices, 3)), "velocity body not three dimensional")
    facets = set()
    for p, q, r in combinations(affine_vertices, 3):
        normal = cross(sub(q, p), sub(r, p))
        g = gcd(*normal)
        if not g:
            continue
        a = tuple(v//g for v in normal)
        b = dot(a, p)
        values = [dot(a, u)-b for u in affine_vertices]
        if max(values) > 0:
            if min(values) < 0:
                continue
            a, b = neg(a), -b
        facets.add((a, b))
    for a, b in facets:
        verify_facet(gains, a, b, 4)
    vertices = set()
    for v in affine_vertices:
        normals = [a for a, b in facets if dot(a, v) == b]
        if any(determinant(c) for c in combinations(normals, 3)):
            vertices.add(v)

    def generate(basis):
        a, b, c = basis
        half = {a, b, c, sub(a, b), sub(a, c), sub(b, c)}
        return half | {neg(x) for x in half}

    frame = next(c for c in combinations(sorted(vertices), 3) if determinant(c) and generate(c) == vertices)
    index = abs(determinant(frame))
    need(len(facets) == 14 and len(vertices) == 12
         and gcd(*(determinant(c) for c in combinations(sorted(vertices), 3))) == index,
         "unexpected certified stable body or lattice index")
    # The unit-radius A3 integer-period ball has leading count
    # (10/3)*m^3 (also from the positive/negative support count);
    # unit hop times divide these velocities by 4.
    return {"square_velocities_realize_all_vertices": True, "all_facets_certified_by_edge_potentials": len(facets),
            "vertex_count": len(vertices), "vertices_are_A3_root_shape_after_real_linear_change": True,
            "integer_basis_for_four_hop_extremal_period_sublattice": frame,
            "index_in_primitive_return_period_lattice": index,
            "stable_body_volume_in_fundamental_cell_units": str(Fraction(5*index, 96))}


def parity_coarsening(graph: Graph, gains: Gains, root: int, coefficients: Vec) -> bool:
    """Test if hop parity equals this functional on closed free periods."""
    address = {root: 0}
    pending = deque([root])
    while pending:
        u = pending.popleft()
        for v in graph[u]:
            expected = (address[u]+1+dot(coefficients, gains[u, v])) % 2
            if v not in address:
                address[v] = expected
                pending.append(v)
            elif address[v] != expected:
                return False
    return True


def finite_null(graph: Graph, gains: Gains, root: int) -> dict[str, object]:
    n = len(next(iter(gains.values())))
    functional = [x for x in product((0, 1), repeat=n) if parity_coarsening(graph, gains, root, x)]
    data = {}
    for modulus in (2, 3):
        arrivals = arrival_minima(graph, gains, root, None, modulus=modulus, keep_parity=True)
        distinct = {x[:-1] for x in arrivals}
        need(len(distinct) == modulus**n, "finite reduction of primitive chart not onto")
        data[modulus] = {"separate_period_residues": len(distinct),
                         "joint_period_and_hop_parity_residues": len(arrivals),
                         "separate_period_residues_by_tick4": len({x[:-1] for x, t in arrivals.items() if t <= 4}),
                         "saturation_time": max(arrivals.values())}
    short = arrival_minima(graph, gains, root, 5, keep_parity=True)
    return {"parity_as_mod2_function_of_free_period": functional,
            "finite_quotient_exhaustion": data,
            "zero_free_period_odd_return_by_tick5": short.get((0,)*n+(1,)),
            "finite_echo_warning": "with fixed modulus the same tracker is finite; its saturation does not establish rank"}


def probe() -> dict[str, object]:
    graph = fixture()
    faces = faces_from_adjacency(graph)
    root = 0
    rooted, words, selected = mark_metric(graph, faces, root, True)
    ranked_two, words_two, selected_two = mark_metric(graph, faces, root, False)
    # Independently evaluate one declared specimen in the nonrooted
    # nine-face orbit; the numbers index the lexicographic oriented
    # adjacency-discovered squares, not spatial coordinates.
    broken = {0, 4, 5, 6, 10, 11, 12, 28, 30}
    need(not set.intersection(*(set(faces[i]) for i in broken)), "specimen unexpectedly has a common root")
    nonrooted, d = primitive_chart(graph, faces, broken, root)
    need(d == 3, "nonrooted comparison does not have rank three")
    census = Counter()
    short_root_counts = Counter()
    for r in graph:
        a = arrival_minima(graph, nonrooted, r, 13)
        profile = tuple(counts_at(range(4, 14), a))
        census[profile] += 1
        short_root_counts[profile[0]] += 1
    rooted_costs = rooted_frontiers(graph, rooted, selected, root)
    two_costs = rooted_frontiers(graph, ranked_two, selected_two, root)
    need(rooted_costs["one_tick_every_edge"]["return_counts_through_ticks_4_to_16"][0] == 13
         and short_root_counts == {3: 4, 5: 8, 7: 4}, "short-time metric discrimination")
    body_root, body_other = (velocity_body_from_squares(w, faces) for w in (rooted, nonrooted))
    need(body_root["index_in_primitive_return_period_lattice"] == 1
         and body_other["index_in_primitive_return_period_lattice"] == 2, "asymptotic lattice index discrimination")
    null_root, null_other, null_two = (finite_null(graph, w, root) for w in (rooted, nonrooted, ranked_two))
    need(not null_root["parity_as_mod2_function_of_free_period"]
         and null_root["zero_free_period_odd_return_by_tick5"] == 5
         and len(null_other["parity_as_mod2_function_of_free_period"]) == 1
         and null_other["zero_free_period_odd_return_by_tick5"] is None,
         "independence/factorization of odd parity")
    need(null_root["finite_quotient_exhaustion"][3]["separate_period_residues_by_tick4"] == 13
         and null_root["finite_quotient_exhaustion"][2]["separate_period_residues_by_tick4"] == 7,
         "counter modulus discriminates or aliases contrary to prediction")
    return {
        "scope": "supplied hop clock on abelian route inventory; no physical metric or field claim",
        "marked_rank_3": {"unit_period_words": words, "fronts": rooted_costs,
                          "normalized_stable_velocity_body": body_root, "finite_counter_control": null_root},
        "same_rank_no_common_root": {
            "all_possible_start_profiles": [{"return_counts_through_ticks_4_to_13": times, "roots": n}
                                            for times, n in sorted(census.items())],
            "normalized_stable_velocity_body": body_other, "finite_counter_control": null_other,
        },
        "marked_rank_2": {"unit_period_words": words_two, "fronts": two_costs, "finite_counter_control": null_two},
        "chart_independent_finite_discriminator": {
            "marked_rank3_classes_by_tick4_including_zero": 13,
            "nonrooted_rank3_classes_by_tick4_from_any_root_including_zero": [3, 5, 7],
        },
        "stable_discriminator": "same real velocity body under a linear change, but index-two fastest period sublattice"
                                " in the nonrooted pattern; volume relative to the full period lattice differs",
    }


if __name__ == "__main__":
    print(json.dumps(probe(), sort_keys=True, separators=(",", ":")))
