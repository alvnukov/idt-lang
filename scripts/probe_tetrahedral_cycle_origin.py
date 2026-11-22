"""Exact finite K4 cycle candidate; no physical probability or QM claim.

Vertices are implementation labels. Directed Hamiltonian tours are identified
only under cyclic change of starting point, not reversal. The edge metric is
the explicitly supplied unit-weight Euclidean metric, not a physical norm.
"""

from __future__ import annotations

import json
from fractions import Fraction
from itertools import combinations, permutations, product

Word = tuple[int, ...]
Flow = tuple[int, ...]
Coord = tuple[Fraction, ...]
Matrix = tuple[Coord, ...]
VERTICES = tuple(range(4))
EDGES = tuple(combinations(VERTICES, 2))
PERMS = tuple(permutations(VERTICES))


def need(condition: bool, message: str) -> None:
    if not condition:
        raise ArithmeticError(message)


def canonical(word: Word) -> Word:
    return min(word[i:] + word[:i] for i in range(len(word)))


def reverse(word: Word) -> Word:
    return canonical(tuple(reversed(word)))


def relabel(word: Word, perm: Word) -> Word:
    return canonical(tuple(perm[x] for x in word))


TOURS = tuple(sorted({canonical(w) for w in PERMS}))
AXES = tuple(w for w in TOURS if w < reverse(w))
TRIANGLES = tuple(sorted({canonical(w) for w in permutations(VERTICES, 3)}))


def flow(word: Word) -> Flow:
    result = [0] * len(EDGES)
    for a, b in zip(word, word[1:] + word[:1], strict=True):
        need(a != b, "self-loop is not a K4 edge")
        edge = (min(a, b), max(a, b))
        result[EDGES.index(edge)] += 1 if a < b else -1
    return tuple(result)


def dot(a: Flow, b: Flow) -> int:
    return sum(x * y for x, y in zip(a, b, strict=True))


def divergence(vector: Flow) -> Flow:
    result = [0] * 4
    for (a, b), value in zip(EDGES, vector, strict=True):
        result[a] -= value
        result[b] += value
    return tuple(result)


HAMILTON = tuple(flow(w) for w in AXES)


def coords(vector: Flow) -> Coord:
    return tuple(Fraction(dot(vector, axis), 4) for axis in HAMILTON)


def reconstruct(point: Coord) -> tuple[Fraction, ...]:
    return tuple(sum((point[i] * HAMILTON[i][j] for i in range(3)), Fraction())
                 for j in range(len(EDGES)))


def determinant(matrix: Matrix) -> Fraction:
    a, b, c = matrix
    return (a[0] * (b[1] * c[2] - b[2] * c[1])
            - a[1] * (b[0] * c[2] - b[2] * c[0])
            + a[2] * (b[0] * c[1] - b[1] * c[0]))


def negate(vector: Flow) -> Flow:
    return tuple(-x for x in vector)


def lattice_controls() -> dict[str, object]:
    need(len(TOURS) == 6 and len(AXES) == 3 and len(TRIANGLES) == 8,
         "directed cycle counts")
    need({flow(w) for w in TOURS} == set(HAMILTON) | {negate(h) for h in HAMILTON},
         "reversal is signed opposition")
    gram = tuple(tuple(dot(a, b) for b in HAMILTON) for a in HAMILTON)
    need(gram == ((4, 0, 0), (0, 4, 0), (0, 0, 4)), "Hamiltonian Gram matrix")
    corners = set(product((Fraction(-1, 2), Fraction(1, 2)), repeat=3))
    need({coords(flow(w)) for w in TRIANGLES} == corners, "all eight half-cube corners")
    need(all(dot(flow(w), flow(w)) == 3 for w in TRIANGLES), "triangle norm")
    need(all(flow(w) == (0,) * 6 for w in permutations(VERTICES, 2)),
         "length-two closed walks only retrace")

    # The star at 0 is a spanning tree. Chord coefficients at 12,13,23
    # uniquely determine an integral divergence-free flow. These triangles
    # have the identity chord-coordinate matrix, so form a full Z-basis.
    chords = tuple(combinations((1, 2, 3), 2))
    fundamental = tuple(flow((0, a, b)) for a, b in chords)
    need(tuple(tuple(t[EDGES.index(e)] for e in chords) for t in fundamental)
         == ((1, 0, 0), (0, 1, 0), (0, 0, 1)), "integral cycle basis")
    # After subtracting the chord-weighted fundamental triangles, a
    # divergence-free flow is supported on the star. Its divergence at
    # vertices 1,2,3 is exactly its three remaining edge coefficients.
    star_units = tuple(tuple(int(i == j) for i in range(6)) for j in range(3))
    star_divergence = tuple(tuple(Fraction(x) for x in divergence(v)[1:])
                            for v in star_units)
    need(determinant(star_divergence) == 1, "tree has no residual flow kernel")
    for vector in (*HAMILTON, *(flow(w) for w in TRIANGLES)):
        need(divergence(vector) == (0,) * 4, "closed flow balance")
        need(reconstruct(coords(vector)) == vector, "coordinate reconstruction")
        need(tuple(sum(vector[EDGES.index(chords[i])] * fundamental[i][j]
                       for i in range(3)) for j in range(6)) == vector,
             "fundamental cycle decomposition")
    volume = abs(determinant(tuple(coords(t) for t in fundamental)))
    need(volume == Fraction(1, 2), "Hamilton lattice index two")
    # Every integral-flow basis generator is in the half-shift coset; the
    # Hamilton axes supply Z^3 and one triangle supplies its half-shift.
    # The determinant index then proves equality, not just a bounded sample.
    half = (Fraction(1, 2),) * 3
    need(half in {coords(flow(w)) for w in TRIANGLES}, "half-shift generator")
    need(all(all((x - Fraction(1, 2)).denominator == 1 for x in coords(t))
             for t in fundamental), "one common half-integral coset")
    # Additional exact bounded control of the general generator statement.
    checked = 0
    for coefficients in product(range(-3, 4), repeat=3):
        vector = tuple(sum(coefficients[i] * fundamental[i][j] for i in range(3))
                       for j in range(6))
        point = coords(vector)
        integer = all(x.denominator == 1 for x in point)
        shifted = all((x - Fraction(1, 2)).denominator == 1 for x in point)
        need(integer or shifted, "cycle lattice is not the two claimed cosets")
        need(dot(vector, vector) == 4 * sum(x * x for x in point), "edge norm transport")
        checked += 1
    return {"directed_tours": 6, "reversal_axes": 3, "oriented_triangles": 8,
            "hamilton_norm_squared": 4, "triangle_norm_squared": 3,
            "hamilton_sublattice_index": 2, "bounded_lattice_controls": checked,
            "cycle_lattice": "Z^3 union (Z+1/2)^3"}


def tour_permutation(word: Word) -> Word:
    result = [0] * 4
    for a, b in zip(word, word[1:] + word[:1], strict=True):
        result[a] = b
    return tuple(result)


def permutation_order(perm: Word) -> int:
    current = tuple(range(len(perm)))
    for n in range(1, 25):
        current = tuple(perm[x] for x in current)
        if current == tuple(range(len(perm))):
            return n
    raise ArithmeticError("unexpected finite permutation order")


def symmetry_controls() -> dict[str, object]:
    matrices = set()
    for perm in PERMS:
        columns = tuple(coords(flow(relabel(w, perm))) for w in AXES)
        matrix = tuple(tuple(columns[j][i] for j in range(3)) for i in range(3))
        need(all(sum(abs(x) for x in row) == 1 for row in matrix), "signed permutation rows")
        need(all(sum(abs(x) for x in column) == 1 for column in columns),
             "signed permutation columns")
        need(determinant(matrix) == 1, "proper rotation orientation")
        matrices.add(matrix)
    need(len(matrices) == 24, "faithful proper cube rotation action")
    for mark in TOURS:
        turn = tour_permutation(mark)
        action = tuple(TOURS.index(relabel(w, turn)) for w in TOURS)
        fixed = {TOURS[i] for i, image in enumerate(action) if i == image}
        need(fixed == {mark, reverse(mark)} and permutation_order(action) == 4,
             "marked tour must fix its axis and cycle the other four labels")
        inverse_turn = tuple(turn.index(i) for i in VERTICES)
        for word in TOURS:
            target = tour_permutation(word)
            conjugate = tuple(turn[target[inverse_turn[i]]] for i in VERTICES)
            need(conjugate == tour_permutation(relabel(word, turn)),
                 "vertex relabeling is exactly permutation conjugation")
        stabilizer = tuple(p for p in PERMS if relabel(mark, p) == mark)
        need(len(stabilizer) == 4 and sorted(map(permutation_order, stabilizer)) == [1, 2, 4, 4],
             "tour stabilizer must be C4")
        fixed_edges = [e for e in EDGES if all(tuple(sorted(p[x] for x in e)) == e
                                               for p in stabilizer)]
        need(not fixed_edges, "no equivariant tour-to-edge assignment, even nonbijective")
        used = {tuple(sorted((a, b))) for a, b in zip(mark, mark[1:] + mark[:1], strict=True)}
        excluded = set(EDGES) - used
        need(len(excluded) == 2 and set.union(*(set(e) for e in excluded)) == set(VERTICES),
             "excluded edges are an opposite pair")
        need({tuple(sorted(turn[x] for x in e)) for e in excluded} == excluded
             and all(tuple(sorted(turn[x] for x in e)) != e for e in excluded),
             "mark selects the opposite pair but not either member")
    edge = EDGES[0]
    edge_stabilizer = tuple(p for p in PERMS if tuple(sorted(p[x] for x in edge)) == edge)
    need(len(edge_stabilizer) == 4
         and sorted(map(permutation_order, edge_stabilizer)) == [1, 2, 2, 2],
         "ordinary edge stabilizer is Klein four, not C4")
    return {"proper_cube_rotations": 24, "tour_stabilizer": "C4",
            "edge_stabilizer": "C2 x C2", "equivariant_tour_to_edge_maps": 0,
            "marked_label_action": "two fixed labels and one four-cycle",
            "excluded_opposite_pair_only": True}


def temporal_controls() -> dict[str, object]:
    for history in permutations(VERTICES, 3):
        missing = tuple(x for x in VERTICES if x not in history)
        need(len(missing) == 1, "unique nonrepeating nonretracing successor")
        successor = missing[0]
        for perm in PERMS:
            image = tuple(perm[x] for x in history)
            need(tuple(x for x in VERTICES if x not in image) == (perm[successor],),
                 "successor is natural under relabeling")
        route = list(history)
        for _ in range(5):
            route.append(next(x for x in VERTICES if x not in route[-3:]))
        need(tuple(route[:4]) == tuple(route[4:8]), "unique successor makes a period-four tour")
    for short_history in ((0,), (0, 1)):
        stabilizer = [p for p in PERMS if all(p[x] == x for x in short_history)]
        candidates = [x for x in VERTICES if x not in short_history]
        need(not any(all(p[x] == x for p in stabilizer) for x in candidates),
             "shorter history cannot pick a natural new vertex")
    a, b = (0, 1, 2), (0, 1, 3)
    loops = (a, b, reverse(a), reverse(b))
    # Concatenate each based loop starting at 0, then freely reduce only
    # immediate edge/inverse-edge pairs. Nonempty reduction means a nontrivial
    # graph path although its signed integral flow vanishes.
    path_edges: list[tuple[int, int]] = []
    for loop in loops:
        need(loop[0] == 0, "based commutator")
        path_edges.extend(zip(loop, loop[1:] + loop[:1], strict=True))
    reduced: list[tuple[int, int]] = []
    for edge in path_edges:
        if reduced and reduced[-1] == (edge[1], edge[0]):
            reduced.pop()
        else:
            reduced.append(edge)
    need(bool(reduced), "commutator accidentally freely trivial")
    need(all(sum(flow(w)[i] for w in loops) == 0 for i in range(6)),
         "homology must erase commutator order")
    # Its chord word is the nonempty freely reduced commutator in two
    # spanning-tree generators: this is an independent path-order witness.
    chord_word = tuple((EDGES.index(tuple(sorted(e))) - 3, 1 if e[0] < e[1] else -1)
                       for e in path_edges if 0 not in e)
    need(chord_word == ((0, 1), (1, 1), (0, -1), (1, -1)), "free chord commutator")
    return {"three_distinct_vertex_histories": 24, "successor": "unique missing vertex",
            "one_or_two_vertex_natural_new_successors": 0,
            "commutator_flow_zero": True, "commutator_reduced_edge_length": len(reduced),
            "homology_forgets_temporal_order": True}


def main() -> None:
    report = {"candidate": "uncolored simple K4 directed-cycle origin",
              "lattice": lattice_controls(), "symmetry": symmetry_controls(),
              "temporal": temporal_controls(),
              "minimality": {
                  "scope": "vertex-minimal connected simple graph with cycle rank three",
                  "reason": "n<=3 gives e-n+1<=1; n=4 needs all six edges",
                  "not_universal": "two vertices and four parallel edges also have cycle rank three",
              },
              "boundaries": [
                  "Finite exact candidate/rival, not a machine-checked universal proof or QM.",
                  "Unit-weight edge L2 metric is supplied; no physical norm or probability follows.",
                  "Conjugation is a transparent label permutation, not derived active dynamics.",
                  "One-mark coupling and path-integral weighting are not derived by passive counting.",
                  "Last-three-vertex memory is supplied to the deterministic successor rule.",
                  "No unconditional claim that K4 is a smaller primitive than three oppositions.",
              ]}
    need(all(n * (n - 1) // 2 - n + 1 < 3 for n in (1, 2, 3)), "simple graph lower bound")
    need(6 - 4 + 1 == 3 and 4 - 2 + 1 == 3, "rank-three graph and multigraph rival")
    print(json.dumps(report, indent=2))


if __name__ == "__main__":
    main()
