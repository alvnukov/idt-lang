"""Exact abelian return periods after selected square reunions are relaxed.

Only the initial fixture uses a folded binary cube to create adjacency.
The calculation discovers square/cube incidences, a spanning tree, and
signed chord relators from that adjacency. A marked two-turn endpoint
splits the root ports into its two common ports and the other three.
Only squares touching those three complementary ROOT edges are freed.
Net crossings of the three edges make integral witnesses; a different
mark or different rule about retained local squares need not do so.

The group computed is the universal **abelian** quotient of return
words under these supplied square relators, not the complete return
language or physical configuration space. Internal modular counters
require a certified return to the same root, reciprocal port identity,
and signed traversal memory. No Euclidean metric, Lorentz structure,
actual dynamics, or physical dimension is inferred.

For the minimal-face comparison let D be the signed cube/face incidence
and R the face/chord relator matrix. D R=0; their exact ranks here imply
ker(D)=im(R) over Q (and R). A possible support of a face-value vector in
ker(D) cannot meet any cube in exactly one face. The union of all such
supports in a broken-face set also satisfies this stopping rule. Thus
enumerating stopping sets through a fixed face, up to size nine, is
enough by face transitivity; a rank computation then produces both
the minimality proof and the distinct minimum-size symmetry classes.
"""

from __future__ import annotations

import json
from collections import Counter, deque
from fractions import Fraction
from itertools import combinations, pairwise, permutations, product

Edge = tuple[int, int]
Graph = dict[int, frozenset[int]]
Face = tuple[int, int, int, int]


def need(condition, why):
    if not condition:
        raise ArithmeticError(why)


def folded_fixture() -> Graph:
    return {v: frozenset(min(v ^ (1 << i), v ^ (1 << i) ^ 31) for i in range(5)) for v in range(16)}


def edge(a: int, b: int) -> Edge:
    return min(a, b), max(a, b)


def travels(cycle):
    return zip(cycle, (*cycle[1:], cycle[0]), strict=True)


def orient_face(graph: Graph, vertices: frozenset[int]) -> Face:
    a = min(vertices)
    b, d = sorted(graph[a] & vertices)
    c, = vertices - {a, b, d}
    need(graph[c] & vertices == {b, d}, "not an induced square")
    return a, b, c, d


def discover_faces(graph: Graph) -> tuple[Face, ...]:
    vertices = {frozenset((a, b, c, d)) for a in graph for b, d in combinations(graph[a], 2)
                for c in (graph[b] & graph[d]) - {a}}
    faces = tuple(sorted(orient_face(graph, quad) for quad in vertices))
    need(len(faces) == 40, "folded carrier square count")
    return faces


def span(graph: Graph, root: int) -> tuple[tuple[Edge, ...], dict[int, int]]:
    parent = {root: root}
    queue = deque([root])
    while queue:
        x = queue.popleft()
        for y in sorted(graph[x]):
            if y not in parent:
                parent[y] = x
                queue.append(y)
    need(set(parent) == set(graph), "spanning tree failed")
    return tuple(sorted(edge(u, v) for u, v in parent.items() if u != v)), parent


def boundary(face: Face, edges: tuple[Edge, ...]) -> tuple[int, ...]:
    oriented = dict.fromkeys(travels(face), 1)
    return tuple(oriented.get((a, b), 0) - oriented.get((b, a), 0) for a, b in edges)


def rational_rank(rows) -> int:
    pivots: dict[int, list[Fraction]] = {}
    for source in rows:
        row = list(map(Fraction, source))
        for i in range(len(row)):
            a = row[i]
            if not a:
                continue
            if i not in pivots:
                pivots[i] = [b/a for b in row]
                break
            row = [b-a*c for b, c in zip(row, pivots[i], strict=True)]
    return len(pivots)


def smith(rows, width: int) -> tuple[int, ...]:
    """Unimodular integer row/column Euclidean operations; nonzero SNF."""
    a = [list(row) for row in rows]
    m = len(a)
    diagonal = []
    for k in range(min(m, width)):
        active = next(((i, j) for i in range(k, m) for j in range(k, width) if a[i][j]), None)
        if active is None:
            break
        i, j = active
        a[k], a[i] = a[i], a[k]
        for row in a:
            row[k], row[j] = row[j], row[k]
        while True:
            if a[k][k] < 0:
                a[k] = [-x for x in a[k]]
            p = a[k][k]
            need(p > 0, "zero pivot inside integer reduction")
            for i in range(k+1, m):
                if a[i][k]:
                    q, remainder = divmod(a[i][k], p)
                    a[i] = [v-q*w for v, w in zip(a[i], a[k], strict=True)]
                    if remainder:
                        a[k], a[i] = a[i], a[k]
                        break
            else:
                for j in range(k+1, width):
                    if a[k][j]:
                        q, remainder = divmod(a[k][j], p)
                        for row in a:
                            row[j] -= q*row[k]
                        if remainder:
                            for row in a:
                                row[k], row[j] = row[j], row[k]
                            break
                else:
                    offender = next((i for i in range(k+1, m) if any(
                        a[i][j] % p for j in range(k+1, width))), None)
                    if offender is None:
                        diagonal.append(p)
                        break
                    # Keeping the pivot fixed, introduce a non-divisible
                    # trailing entry into its row; the next column pass
                    # then strictly decreases the positive Euclidean pivot.
                    a[k] = [v+w for v, w in zip(a[k], a[offender], strict=True)]
    need(all(a[i][j] == (diagonal[i] if i == j and i < len(diagonal) else 0)
             for i in range(m) for j in range(width)), "Smith reduction left a non-diagonal entry")
    need(all(y % x == 0 for x, y in pairwise(diagonal)), "not Smith invariant factors")
    return tuple(diagonal)


def assess(rows: tuple[tuple[int, ...], ...], broken: set[int], width: int) -> dict[str, object]:
    retained = [r for i, r in enumerate(rows) if i not in broken]
    invariants = smith(retained, width)
    return {"freed_faces": len(broken), "free_rank": width-len(invariants),
            "torsion_invariant_factors": [d for d in invariants if d > 1]}


def root_breaks(faces: tuple[Face, ...], root: int, ports: tuple[int, ...]) -> set[int]:
    selected = {edge(root, v) for v in ports}
    return {i for i, f in enumerate(faces) if selected.intersection(edge(u, v) for u, v in travels(f))}


def root_profiles(graph: Graph, faces: tuple[Face, ...], rows, width: int) -> list[dict[str, object]]:
    expected_face_counts = (0, 4, 7, 9, 10, 10)
    expected_ranks = (0, 1, 2, 3, 4, 4)
    result = []
    for m in range(6):
        signatures = set()
        tested = 0
        for root, ns in graph.items():
            for ports in combinations(sorted(ns), m):
                broken = root_breaks(faces, root, ports)
                a = assess(rows, broken, width)
                signatures.add((a["freed_faces"], a["free_rank"], tuple(a["torsion_invariant_factors"])))
                tested += 1
        need(len(signatures) == 1, "root/port label symmetry was lost")
        count, rank, torsion = next(iter(signatures))
        need(count == expected_face_counts[m] and rank == expected_ranks[m], "root-edge rank profile")
        result.append({"selected_root_ports": m, "freed_faces": count, "free_rank": rank,
                       "torsion_invariant_factors": torsion, "root_subset_tests": tested})
    return result


def cube_vertex_sets(graph: Graph) -> tuple[frozenset[int], ...]:
    cubes = set()
    for root in graph:
        for port in combinations(graph[root], 3):
            second = tuple(next(iter((graph[x] & graph[y]) - {root})) for x, y in combinations(port, 2))
            opposite = frozenset.intersection(*(graph[x] for x in second))
            need(len(opposite) == 1, "cube opposite corner not uniquely determined by adjacency")
            cube = frozenset((root, *port, *second, *opposite))
            need(len(cube) == 8 and all(len(graph[v] & cube) == 3 for v in cube), "not an induced combinatorial cube")
            cubes.add(cube)
    need(len(cubes) == 20, "folded carrier cube count")
    return tuple(sorted(cubes, key=lambda c: tuple(sorted(c))))


def cube_coordinates(graph: Graph, c: frozenset[int]) -> dict[int, int]:
    p = min(c)
    ports = tuple(sorted(graph[p] & c))
    words = {0: p, **{1 << i: v for i, v in enumerate(ports)}}
    for i, j in combinations(range(3), 2):
        words[(1 << i) | (1 << j)], = (graph[ports[i]] & graph[ports[j]] & c) - {p}
    words[7], = c - set(words.values())
    need(all({words[k ^ (1 << j)] for j in range(3)} == graph[v] & c for k, v in words.items()),
         "cube coordinates are not derived")
    return words


def signed_face_lookup(faces: tuple[Face, ...]) -> dict[Face, tuple[int, int]]:
    signs = {}
    for i, f in enumerate(faces):
        for sign, cycle in ((1, f), (-1, f[::-1])):
            for j in range(4):
                signs[cycle[j:] + cycle[:j]] = (i, sign)
    return signs


def cube_boundaries(graph: Graph, faces: tuple[Face, ...]) -> tuple[tuple[int, ...], ...]:
    lookup = signed_face_lookup(faces)
    rows = []
    for cube in cube_vertex_sets(graph):
        words = cube_coordinates(graph, cube)
        row = [0] * len(faces)
        for j in range(3):
            a, b = (1 << i for i in range(3) if i != j)
            for v in (0, 1):
                c = v << j
                f = tuple(words[k] for k in (c, c ^ a, c ^ a ^ b, c ^ b))
                i, sign = lookup[f]
                row[i] = (-1)**j * (2*v-1)*sign
        need(sum(bool(x) for x in row) == 6, "signed cube boundary does not contain six faces")
        rows.append(tuple(row))
    need(all(sum(row[i] != 0 for row in rows) == 3 for i in range(len(faces))),
         "each square should meet three cubes")
    return tuple(rows)


def base_chart(graph: Graph, root: int) -> dict[int, int]:
    ports = {u: 1 << i for i, u in enumerate(sorted(graph[root]))}
    chart = {root: 0, **ports}
    for v in graph.keys() - chart.keys():
        chart[v] = sum(ports[u] for u in graph[v] & graph[root])
    return chart


def verify_face_transitivity(graph: Graph, faces: tuple[Face, ...]) -> tuple[tuple[int, ...], ...]:
    chart = base_chart(graph, min(graph))
    lookup = {frozenset(f): i for i, f in enumerate(faces)}
    actions = []
    for root in graph:
        inverse = {x: u for u, x in base_chart(graph, root).items()}
        need(len(inverse) == len(graph), "root and port pairs do not distinguish all vertices")
        for ports in permutations((1, 2, 4, 8, 16)):
            def permute(mask, ports=ports):
                return sum(bit for i, bit in enumerate(ports) if mask & (1 << i))

            move = {u: inverse[permute(v)] for u, v in chart.items()}
            need(all({move[w] for w in row} == graph[move[u]] for u, row in graph.items()), "not an automorphism")
            actions.append(tuple(1 << lookup[frozenset(move[v] for v in f)] for f in faces))
    need({a[0] for a in actions} == {1 << i for i in range(len(faces))},
         "first-square reduction does not cover all faces")
    return tuple(actions)


def masks(bits: int):
    while bits:
        b = bits & -bits
        yield b
        bits ^= b


def stopping_sets(d: tuple[tuple[int, ...], ...], bound: int = 8) -> tuple[set[int], list[int]]:
    n = len(d[0])
    cubes = tuple(sum(1 << i for i, v in enumerate(row) if v) for row in d)
    all_faces = (1 << n) - 1
    visited, todo, stopping = {1}, [1], []
    while todo:
        chosen = todo.pop()
        size = chosen.bit_count()
        unfinished = next((c for c in cubes if (c & chosen).bit_count() == 1), None)
        if unfinished is None:
            stopping.append(chosen)
        if size == bound:
            continue
        # A compatible target superset must add another face from this
        # cube. Once no cube is pending, allow all possible extensions.
        allowed = (all_faces if unfinished is None else unfinished) & ~chosen
        for b in masks(allowed):
            child = chosen | b
            if child not in visited:
                visited.add(child)
                todo.append(child)
    return visited, stopping


def classify_minimal_orbits(anchored, actions, graph, faces, rows, width):
    rooted = {sum(1 << i for i in root_breaks(faces, r, ports))
              for r, ns in graph.items() for ports in combinations(sorted(ns), 3)}
    all_rank_three = set()
    remaining = set(anchored)
    result = []
    while remaining:
        seed = min(remaining)
        cols = tuple(b.bit_length()-1 for b in masks(seed))
        orbit = {sum(a[i] for i in cols) for a in actions}
        anchor_part = {s for s in orbit if s & 1}
        need(anchor_part <= remaining and not all_rank_three.intersection(orbit), "inconsistent symmetry orbit")
        remaining.difference_update(anchor_part)
        all_rank_three.update(orbit)
        is_rooted = seed in rooted
        common_vertices = set.intersection(*(set(faces[i]) for i in cols))
        need((orbit <= rooted if is_rooted else orbit.isdisjoint(rooted))
             and bool(common_vertices) == is_rooted, "rank-three minimum frame orbit not invariant")
        smith_rep = assess(rows, set(cols), width)
        need(smith_rep["free_rank"] == 3, "independent integer confirmation of real-rank orbit")
        counts = Counter(v for i in cols for v in faces[i])
        result.append({"size": len(orbit), "through_first_face": len(anchor_part),
                       "root_edge_triple_frame": is_rooted, "common_vertex": bool(common_vertices),
                       "representative": cols, "vertex_face_incidence_histogram": dict(Counter(counts.values())),
                       "return_group": smith_rep})
    need(rooted <= all_rank_three and len(all_rank_three)*9 == len(anchored)*len(faces),
         "minimal family census disagrees with face transitivity")
    return result


def minimum_search(graph, faces, rows, edges, width):
    d = cube_boundaries(graph, faces)
    b = tuple(boundary(f, edges) for f in faces)
    need(all(sum(d[i][k]*b[k][j] for k in range(len(faces))) == 0
             for i in range(len(d)) for j in range(len(edges))), "boundary of boundary not zero")
    rank_d = rational_rank(d)
    rank_r = rational_rank(rows)
    need(rank_d == 15 and rank_r == width == 25 and rank_d+rank_r == len(faces),
         "cube kernel not necessarily the face-value image")
    face_actions = verify_face_transitivity(graph, faces)
    visited, stopping = stopping_sets(d, 9)
    freqs: Counter = Counter()
    by_size: dict[int, int] = {}
    min_rank3 = set()
    for s in stopping:
        columns = tuple(b.bit_length()-1 for b in masks(s))
        rank = rational_rank(tuple(row[j] for j in columns) for row in d)
        nullity = len(columns) - rank
        freqs[len(columns), nullity] += 1
        by_size[len(columns)] = max(by_size.get(len(columns), 0), nullity)
        if len(columns) == 9 and nullity >= 3:
            need(nullity == 3, "there is also rank four at the minimum size")
            min_rank3.add(s)
    classes = classify_minimal_orbits(min_rank3, face_actions, graph, faces, rows, width)
    return {"minimum_size_tested_through": 9, "signed_cube_rank": rank_d, "signed_face_rank": rank_r,
            "face_orbit_size": len({a[0] for a in face_actions}), "anchored_partial_supports_visited": len(visited),
            "anchored_stopping_supports_by_size_and_nullity": [
                {"size": size, "nullity": dim, "count": n} for (size, dim), n in sorted(freqs.items())],
            "max_nullity_by_size": dict(sorted(by_size.items())),
            "some_size_le_8_has_rank_at_least_3": any(k <= 8 and dim >= 3 for k, dim in by_size.items()),
            "global_size_9_rank_3_sets": sum(c["size"] for c in classes),
            "size_9_rank_3_symmetry_classes": classes}


def crossing(word: tuple[int, ...], root: int, ports: tuple[int, ...]) -> tuple[int, ...]:
    e = Counter(pairwise(word))
    return tuple(e[root, p] - e[p, root] for p in ports)


def odd_loop_avoiding_ports(graph: Graph, root: int, ports: tuple[int, ...]) -> tuple[int, ...]:
    first, goal = (root, 0), (root, 1)
    blocked = {edge(root, v) for v in ports}
    parent = {first: None}
    todo = deque([first])
    while todo and goal not in parent:
        u, p = todo.popleft()
        for v in sorted(graph[u]):
            next_state = v, 1-p
            if edge(u, v) not in blocked and next_state not in parent:
                parent[next_state] = (u, p)
                todo.append(next_state)
    need(goal in parent, "no independent odd return")
    path = []
    x = goal
    while x is not None:
        path.append(x[0])
        x = parent[x]
    return tuple(reversed(path))


def periods(graph: Graph, faces: tuple[Face, ...], root: int, mark: int, *, complement: bool) -> dict[str, object]:
    common = graph[root] & graph[mark]
    other = graph[root] - common
    need(len(common) == 2 and len(other) == 3, "marked pair does not give the two/three root frame")
    ports = tuple(sorted(other if complement else common))
    kept_port = min(graph[root] - set(ports))
    broken = root_breaks(faces, root, ports)
    loops = []
    for p in ports:
        u, = (graph[p] & graph[kept_port]) - {root}
        loops.append((root, p, u, kept_port, root))
    expected = tuple(tuple(int(i == j) for j in range(len(ports))) for i in range(len(ports)))
    need(tuple(crossing(w, root, ports) for w in loops) == expected, "period loops are not integral unit witnesses")
    need(all(not any(crossing((*f, f[0]), root, ports)) for i, f in enumerate(faces) if i not in broken),
         "period does not annihilate an intact square")
    odd = odd_loop_avoiding_ports(graph, root, ports)
    need((len(odd)-1) % 2 == 1 and not any(crossing(odd, root, ports)), "odd direction overlaps free witnesses")
    mod2_and_3 = {}
    for modulus in (2, 3):
        residues = set()
        for counts in product(range(modulus), repeat=len(ports)):
            word = (root,)
            for w, repeat in zip(loops, counts, strict=True):
                word += w[1:]*repeat
            period = tuple(x % modulus for x in crossing(word, root, ports))
            residues.add((period, (len(word)-1) % 2))
            extended = word + odd[1:]
            residues.add((tuple(x % modulus for x in crossing(extended, root, ports)), (len(extended)-1) % 2))
        need(len(residues) == modulus**len(ports)*2, "finite quotient census")
        mod2_and_3[modulus] = len(residues)
    return {"selected_local_port_count": len(ports), "ordered_two_turn_frame": [root, min(common), mark],
            "unselected_baseline_port": kept_port,
            "example_loops_fixture_vertex_names_only": loops, "independent_odd_loop": odd,
            "unit_net_crossing_vectors": expected, "reachable_counter_residues_including_odd_parity": mod2_and_3,
            "assumptions": "root identity, reciprocal port counters, supplied retained square relations and abelianization"}


def probe() -> dict[str, object]:
    graph = folded_fixture()
    faces = discover_faces(graph)
    edges = tuple(sorted({edge(u, v) for u, row in graph.items() for v in row}))
    root = min(graph)
    tree, _ = span(graph, root)
    chords = tuple(sorted(set(edges) - set(tree)))
    need(len(edges) == 40 and len(tree) == 15 and len(chords) == 25, "cycle basis dimension")
    rows = tuple(boundary(f, chords) for f in faces)
    need(smith(((2, 0), (0, 3)), 2) == (1, 6) and smith(((2, 4), (3, 9)), 2) == (1, 6),
         "nontrivial Smith arithmetic controls")
    root_report = root_profiles(graph, faces, rows, len(chords))
    need(root_report[0]["torsion_invariant_factors"] == (2,), "complete carrier return group is not Z2")
    marking = min(graph.keys() - graph[root] - {root})
    marked = periods(graph, faces, root, marking, complement=True)
    alternative = assess(rows, root_breaks(faces, root, tuple(graph[root] & graph[marking])), len(chords))
    alternative_periods = periods(graph, faces, root, marking, complement=False)
    minimum = minimum_search(graph, faces, rows, edges, len(chords))
    different_nine = assess(rows, set(range(0, 36, 4)), len(chords))
    return {"scope": "exact universal abelian relator quotient, not physical space or observational sufficiency",
            "vertices": len(graph), "edges": len(edges), "squares": len(faces),
            "spanning_tree_edges": len(tree), "cycle_generators": len(chords),
            "root_edge_profile": root_report, "marked_complement_3": marked,
            "marked_common_2": {"return_group": alternative, "periods": alternative_periods},
            "different_nine_faces": different_nine,
            "minimum_rank_three_faces_if_bound_passes": 9 if not minimum["some_size_le_8_has_rank_at_least_3"] else None,
            "minimal_support_audit": minimum}


if __name__ == "__main__":
    print(json.dumps(probe(), sort_keys=True, separators=(",", ":")))
