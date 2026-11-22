"""Uncolored graph quarter-turns and the separate abelian-neutrality premise.

CONCEPTUAL HIT. The loopless multigraph with vertices O,A,B and two parallel
O--A edges e1,e2 and two O--B edges f1,f2 has an ordinary incidence
automorphism e1->f1->e2->f2->e1, swapping A,B. Its FULL integral cycle
lattice has rank two, with a=e2-e1, b=f2-f1. The induced action is
a->b, b->-a. The signed quarter-turn is therefore induced by an uncolored
graph automorphism, not inserted as a matrix operation. The edge-square
form restricts to 2(a^2+b^2). Distinct parallel channels are supplied even
though they have no colors. Identifying parallel edges instead gives a tree.
If loops are allowed AND their two half-edges are retained as incidence data,
a one-vertex/two-loop rose is smaller still: a four-cycle of its half-edges
induces J. An edge-only multigraph convention that discards loop flips does
not encode that operation. The main constructions here are loopless to avoid
silently changing this automorphism convention.

For SIMPLE undirected graphs, the smallest such graph has 5 vertices and
6 edges: two triangles sharing one vertex (the bowtie). A four-cycle of
the outer vertices induces the same J on all H1; the form is 3(a^2+b^2).
Connected simple graphs with first Betti number two are enumerated up to
isomorphism through 5 vertices below. No smaller graph qualifies. More
generally, removing hanging trees and suppressing degree-two subdivisions
leaves a rank-two core of rose/figure-eight, theta, or dumbbell type. Theta
actions on H1 factor through S3 x C2 and have orders 1,2,3,6, never 4.
Equal cactus cycles can be exchanged with one reflection to give J; unequal
lengths or asymmetric attachments may forbid that automorphism. Tree-only
automorphisms can have order four but act trivially on H1 and do not count.

WHAT IS SUPPLIED. H1 is the kernel of the INTEGER incidence map. Choosing
directions to write that map is coordinate bookkeeping, not a directed-edge
structure; all coordinate reorientations are checked. But integer chains,
their addition, and the decision to identify walks with their net chains are
mathematical constructions, not consequences of positive path composition.
An unweighted quadratic edge stock is one explicit invariant metric. Word
length and other invariant readouts also exist; a quadratic physical norm,
Born rule, detector, serial multiplication and physical phase are not derived.

ORIENTATION WALL. If a directed-graph automorphism preserves arrows and acts
as J^2=-I on ALL H1, the directed graph has no directed cycle. A directed
cycle would be a nonzero nonnegative circulation z; arrow preservation keeps
J^2 z nonnegative, while J^2 z=-z. The multigraph hit admits a source-to-sinks
orientation, hence has no nontrivial directed loops. The simple bowtie J has
NO invariant edge orientation: its square reverses an edge in each triangle.
Two squares sharing a vertex (7 vertices,8 edges) admit an invariant acyclic
orientation. These directed realizations still need reversible walks to form
nontrivial loop histories; positive directed composition does not suffice.

NO CANONICAL J. The unmarked bowtie's full automorphism action is D8. A cycle
reflection conjugates J to J^-1. Commuting with diag(1,-1) and the cycle swap
forces any naturally distinguished linear endomorphism to be scalar, so it
cannot square to -I. The unordered pair {J,J^-1}, or the C4 subgroup, IS
invariant; choosing its positive generator needs extra orientation/reference
structure. Coordinate labels do not make that selection canonical.

PLANARITY IS NOT THAT EXTRA STRUCTURE. On a fixed planar rank-two embedding,
the two bounded-face orientations are either permuted or both reversed by
an ambient homeomorphism. Its H1 action is in +/-S2, with no quarter-turn.
The bowtie's abstract J does not preserve or globally reverse its planar
rotation system. Interleaving the four central half-edges gives an oriented
ribbon graph on which J is the positive cyclic shift, but its thickening has
genus one and ONE boundary, not a planar embedding with three boundaries.
Filling that boundary adds a commutator 2-cell and gives a torus. That yields
Z^2 topologically only after adding the explicit surface/face relation.

NEUTRALITY WALL / QUICK DISCRIMINATOR. Unoriented reversible walks modulo
local spur deletion e e^-1 form the free loop group F2, not Z^2. The words
  a b a^-1 b^-1  and  a a^-1 b b^-1
have identical oriented edge counts and length, but only the latter reduces
to idle by spurs. Net flow erases the first word via EXTRA abelianization.
The J automorphism respects both models and preserves their word metrics.
A C4-invariant toy readout W=(1+reduced_length^2)*(net_a^2+net_b^2) makes
both words dark alone yet gives 26 versus 2 after the SAME appended a.
This is a graph-native history countercontrol, not a physical detector model.

The next physical discriminator would compare those equal-edge-count paths
coherently, then apply common continuation contexts while retaining all output
and apparatus records. Matched delays and path records require independent
calibration. No observed experiment is claimed here, and ordinary interference
alone does not establish universal spur/homology neutrality. The neighboring
probe_unsigned_neutral_motifs supplies opposite-pair congruences before taking
a commutative quotient; here the graph generates the C4 action geometrically
but does not silently supply that congruence. No Lean or physics status upgrade.
"""

from __future__ import annotations

import argparse
import json
import unittest
from collections import Counter, deque
from dataclasses import dataclass
from itertools import combinations, permutations, product

Edge = tuple[int, int]
Vector = tuple[int, ...]
Matrix2 = tuple[tuple[int, int], tuple[int, int]]
IDENTITY: Matrix2 = ((1, 0), (0, 1))
NEGATIVE: Matrix2 = ((-1, 0), (0, -1))
J: Matrix2 = ((0, -1), (1, 0))


def need(condition: bool, message: str) -> None:
    if not condition:
        raise AssertionError(message)


@dataclass(frozen=True)
class Graph:
    vertices: int
    edges: tuple[Edge, ...]

    def __post_init__(self) -> None:
        if self.vertices < 1 or any(
            not 0 <= u < v < self.vertices for u, v in self.edges
        ):
            raise ValueError(
                "loopless graph with reference-oriented edges u<v required"
            )

    def connected(self) -> bool:
        found = {0}
        while True:
            expanded = (
                found
                | {v for u, v in self.edges if u in found}
                | {u for u, v in self.edges if v in found}
            )
            if expanded == found:
                return len(found) == self.vertices
            found = expanded

    def boundary(self, chain: Vector) -> Vector:
        result = [0] * self.vertices
        for value, (u, v) in zip(chain, self.edges, strict=True):
            result[u] -= value
            result[v] += value
        return tuple(result)


@dataclass(frozen=True)
class Automorphism:
    vertices: tuple[int, ...]
    edges: tuple[int, ...]

    def chain(self, graph: Graph, values: Vector) -> Vector:
        result = [0] * len(graph.edges)
        for index, (u, v) in enumerate(graph.edges):
            sign = 1 if self.vertices[u] < self.vertices[v] else -1
            result[self.edges[index]] += sign * values[index]
        return tuple(result)

    def darts(self, graph: Graph) -> tuple[int, ...]:
        result = []
        for edge, (u, v) in enumerate(graph.edges):
            target = self.edges[edge]
            for vertex in (u, v):
                result.append(
                    2 * target + int(self.vertices[vertex] != graph.edges[target][0])
                )
        return tuple(result)


def automorphisms(graph: Graph) -> tuple[Automorphism, ...]:
    classes: dict[Edge, list[int]] = {}
    for index, edge in enumerate(graph.edges):
        classes.setdefault(edge, []).append(index)
    output = []
    for vertices in permutations(range(graph.vertices)):
        targets = []
        for (u, v), old in classes.items():
            target = classes.get(
                (min(vertices[u], vertices[v]), max(vertices[u], vertices[v])), []
            )
            if len(target) != len(old):
                break
            targets.append(tuple(permutations(target)))
        else:
            for images in product(*targets):
                edges = [0] * len(graph.edges)
                for old, new in zip(classes.values(), images, strict=True):
                    for source, target_index in zip(old, new, strict=True):
                        edges[source] = target_index
                output.append(Automorphism(vertices, tuple(edges)))
    return tuple(output)


def cycle_basis(graph: Graph) -> tuple[tuple[Vector, Vector], tuple[int, int]]:
    need(
        graph.connected() and len(graph.edges) - graph.vertices + 1 == 2,
        "connected first Betti number two",
    )
    components = list(range(graph.vertices))
    tree: list[int] = []
    chords: list[int] = []
    for index, (u, v) in enumerate(graph.edges):
        if components[u] == components[v]:
            chords.append(index)
        else:
            old, new = components[v], components[u]
            components = [new if item == old else item for item in components]
            tree.append(index)
    cycles = []
    for chord in chords:
        u, v = graph.edges[chord]
        parents: dict[int, tuple[int, int]] = {}
        queue = deque([v])
        seen = {v}
        while queue:
            vertex = queue.popleft()
            for index in tree:
                a, b = graph.edges[index]
                neighbor = b if a == vertex else a if b == vertex else -1
                if neighbor >= 0 and neighbor not in seen:
                    seen.add(neighbor)
                    parents[neighbor] = (vertex, index)
                    queue.append(neighbor)
        values = [0] * len(graph.edges)
        values[chord] = 1
        here = u
        while here != v:
            previous, index = parents[here]
            values[index] += 1 if graph.edges[index] == (previous, here) else -1
            here = previous
        cycle = tuple(values)
        need(
            graph.boundary(cycle) == (0,) * graph.vertices,
            "fundamental cycle has zero boundary",
        )
        cycles.append(cycle)
    need(len(cycles) == len(chords) == 2, "full rank-two lattice, not selected plane")
    return (cycles[0], cycles[1]), (chords[0], chords[1])


def matrix_product(a: Matrix2, b: Matrix2) -> Matrix2:
    rows = tuple(
        tuple(sum(a[i][k] * b[k][j] for k in range(2)) for j in range(2))
        for i in range(2)
    )
    return (rows[0][0], rows[0][1]), (rows[1][0], rows[1][1])


def cycle_action(graph: Graph, auto: Automorphism) -> Matrix2:
    basis, chords = cycle_basis(graph)
    images = tuple(auto.chain(graph, cycle) for cycle in basis)
    matrix: Matrix2 = (
        (images[0][chords[0]], images[1][chords[0]]),
        (images[0][chords[1]], images[1][chords[1]]),
    )
    for j in range(2):
        need(
            images[j]
            == tuple(
                sum(matrix[i][j] * basis[i][edge] for i in range(2))
                for edge in range(len(graph.edges))
            ),
            "integral full-cycle action",
        )
    for i in range(2):
        for j in range(2):
            need(
                sum(a * b for a, b in zip(images[i], images[j], strict=True))
                == sum(a * b for a, b in zip(basis[i], basis[j], strict=True)),
                "inherited edge-square isometry",
            )
    return matrix


def has_j(graph: Graph) -> bool:
    return any(
        matrix_product(action, action) == NEGATIVE
        for auto in automorphisms(graph)
        for action in (cycle_action(graph, auto),)
    )


def action_order(action: Matrix2) -> int:
    power = IDENTITY
    for exponent in range(1, 13):
        power = matrix_product(power, action)
        if power == IDENTITY:
            return exponent
    raise AssertionError("finite rank-two graph action exceeded this census bound")


def canonical_edges(graph: Graph) -> tuple[Edge, ...]:
    return min(
        tuple(
            sorted(
                (min(order[u], order[v]), max(order[u], order[v]))
                for u, v in graph.edges
            )
        )
        for order in permutations(range(graph.vertices))
    )


def simple_census() -> list[dict[str, object]]:
    output: list[dict[str, object]] = []
    for vertices in range(1, 6):
        available = tuple(combinations(range(vertices), 2))
        types: set[tuple[Edge, ...]] = set()
        labeled = 0
        for edges in combinations(available, vertices + 1):
            graph = Graph(vertices, edges)
            if graph.connected():
                labeled += 1
                types.add(canonical_edges(graph))
        hits = [edges for edges in sorted(types) if has_j(Graph(vertices, edges))]
        classifications = []
        for edges in sorted(types):
            graph = Graph(vertices, edges)
            autos = automorphisms(graph)
            orders = sorted({action_order(cycle_action(graph, auto)) for auto in autos})
            classifications.append(
                {"edges": edges, "automorphisms": len(autos), "whole_H1_orders": orders}
            )
        if vertices < 5:
            need(not hits, "no smaller simple whole-lattice quarter-turn")
        else:
            need(len(hits) == 1, "unique minimal simple isomorphism type")
            degrees = sorted(
                sum(vertex in edge for edge in hits[0]) for vertex in range(vertices)
            )
            need(
                degrees == [2, 2, 2, 2, 4],
                "minimal type is two triangles sharing one vertex",
            )
        output.append(
            {
                "vertices": vertices,
                "edges": vertices + 1,
                "connected_labeled_graphs": labeled,
                "isomorphism_types": len(types),
                "whole_H1_J_types": len(hits),
                "type_controls": classifications,
            }
        )
    return output


MULTI = Graph(3, ((0, 1), (0, 1), (0, 2), (0, 2)))
BOWTIE = Graph(5, ((0, 1), (0, 2), (0, 3), (0, 4), (1, 2), (3, 4)))
SQUARES = Graph(7, ((0, 1), (0, 3), (0, 4), (0, 6), (1, 2), (2, 3), (4, 5), (5, 6)))


def j_automorphism(graph: Graph) -> Automorphism:
    return next(auto for auto in automorphisms(graph) if cycle_action(graph, auto) == J)


def directed_acyclic(graph: Graph, arrows: Vector) -> bool:
    edges = tuple(
        (u, v) if sign == 1 else (v, u)
        for sign, (u, v) in zip(arrows, graph.edges, strict=True)
    )
    remaining = set(range(graph.vertices))
    while remaining:
        sources = {
            vertex
            for vertex in remaining
            if not any(v == vertex and u in remaining for u, v in edges)
        }
        if not sources:
            return False
        remaining -= sources
    return True


def orientation_controls(graph: Graph) -> int:
    auto = j_automorphism(graph)
    basis, _ = cycle_basis(graph)
    count = 0
    for signs in product((-1, 1), repeat=len(graph.edges)):
        # S A S is the same chain map in reversed coordinate edge directions.
        changed_basis = tuple(
            tuple(sign * value for sign, value in zip(signs, cycle, strict=True))
            for cycle in basis
        )
        for index, cycle in enumerate(changed_basis):
            old = tuple(sign * value for sign, value in zip(signs, cycle, strict=True))
            image = tuple(
                sign * value
                for sign, value in zip(signs, auto.chain(graph, old), strict=True)
            )
            need(
                image
                == tuple(
                    sum(J[i][index] * changed_basis[i][edge] for i in range(2))
                    for edge in range(len(graph.edges))
                ),
                "coordinate edge orientation does not impose J",
            )
        if auto.chain(graph, signs) == signs:
            count += 1
            need(
                directed_acyclic(graph, signs),
                "every invariant arrow orientation is acyclic",
            )
    return count


def symmetry_controls() -> dict[str, object]:
    # A rose with loop-half-edges 0,2 paired and 1,3 paired. Keeping those
    # flags permits loop reversal; a vertex/edge-only convention loses it.
    opposite, rotation = (2, 3, 0, 1), (1, 2, 3, 0)
    need(
        all(rotation[opposite[d]] == opposite[rotation[d]] for d in range(4)),
        "rose half-edge quarter-turn preserves unoriented edge pairing",
    )
    columns = []
    for source in (0, 1):
        target = rotation[source]
        columns.append(
            tuple(
                (1 if target < 2 else -1) * int(target % 2 == axis) for axis in range(2)
            )
        )
    need(
        ((columns[0][0], columns[1][0]), (columns[0][1], columns[1][1])) == J,
        "one-vertex two-loop hit requires half-edge automorphism convention",
    )
    for graph, length in ((MULTI, 2), (BOWTIE, 3), (SQUARES, 4)):
        basis, _ = cycle_basis(graph)
        gram = tuple(
            tuple(sum(a * b for a, b in zip(x, y, strict=True)) for y in basis)
            for x in basis
        )
        need(
            gram == ((length, 0), (0, length)),
            "equal cactus cycle lengths supply square lattice form",
        )
        need(
            cycle_action(graph, j_automorphism(graph)) == J,
            "graph-induced quarter-turn",
        )
    actions = {cycle_action(BOWTIE, auto) for auto in automorphisms(BOWTIE)}
    reflection: Matrix2 = ((1, 0), (0, -1))
    swap: Matrix2 = ((0, 1), (1, 0))
    inverse_j: Matrix2 = ((0, 1), (-1, 0))
    need(
        len(actions) == 8 and reflection in actions and swap in actions,
        "full D8 action",
    )
    need(
        matrix_product(matrix_product(reflection, J), reflection) == inverse_j,
        "reflection reverses quarter-turn",
    )
    need(
        {a for a in actions if matrix_product(a, a) == NEGATIVE} == {J, inverse_j},
        "canonical unordered pair, not canonical generator",
    )
    # Universal centralizer calculation by coefficients: K R=R K forces
    # K01=K10=0; K swap=swap K then forces K00=K11. Finite regression:
    for a, b, c, d in product(range(-2, 3), repeat=4):
        matrix: Matrix2 = ((a, b), (c, d))
        commutes = matrix_product(matrix, reflection) == matrix_product(
            reflection, matrix
        ) and matrix_product(matrix, swap) == matrix_product(swap, matrix)
        need(commutes == (b == c == 0 and a == d), "scalar centralizer regression")
    theta = Graph(2, ((0, 1),) * 3)
    orders = set()
    for auto in automorphisms(theta):
        action, power = cycle_action(theta, auto), IDENTITY
        for exponent in range(1, 7):
            power = matrix_product(power, action)
            if power == IDENTITY:
                orders.add(exponent)
                break
        need(
            matrix_product(action, action) != NEGATIVE,
            "theta no quarter-turn on whole H1",
        )
    need(orders == {1, 2, 3, 6}, "theta S3 x C2 orders")
    counts = [orientation_controls(graph) for graph in (MULTI, BOWTIE, SQUARES)]
    need(
        counts[0] > 0 and counts[1] == 0 and counts[2] > 0,
        "directed and unoriented distinctions",
    )
    return {
        "rose_with_retained_half_edges_vertices_edges": [1, 2],
        "multigraph_vertices_edges": [3, 4],
        "simple_minimum_vertices_edges": [5, 6],
        "bowtie_automorphisms": len(actions),
        "theta_H1_orders": sorted(orders),
        "invariant_arrow_orientations_multi_triangles_squares": counts,
        "canonical_J": False,
        "canonical_unordered_J_pair": True,
    }


def rotation_system(graph: Graph, center_order: tuple[int, ...]) -> tuple[int, ...]:
    around: list[list[int]] = [[] for _ in range(graph.vertices)]
    for index, (u, v) in enumerate(graph.edges):
        around[u].append(2 * index)
        around[v].append(2 * index + 1)
    need(set(around[0]) == set(center_order), "complete central rotation")
    around[0] = list(center_order)
    rotation = [0] * (2 * len(graph.edges))
    for darts in around:
        for here, following in zip(darts, darts[1:] + darts[:1], strict=True):
            rotation[here] = following
    return tuple(rotation)


def permutation_cycles(mapping: tuple[int, ...]) -> tuple[tuple[int, ...], ...]:
    remaining = set(range(len(mapping)))
    cycles = []
    while remaining:
        here = min(remaining)
        cycle = []
        while here in remaining:
            remaining.remove(here)
            cycle.append(here)
            here = mapping[here]
        cycles.append(tuple(cycle))
    return tuple(cycles)


def ribbon_controls() -> dict[str, object]:
    planar = rotation_system(BOWTIE, (0, 2, 4, 6))
    interleaved = rotation_system(BOWTIE, (0, 4, 2, 6))
    boundary_words = []
    boundaries = []
    auto = j_automorphism(BOWTIE)
    dart_map = auto.darts(BOWTIE)
    for rotation in (planar, interleaved):
        boundaries.append(
            permutation_cycles(tuple(rotation[dart ^ 1] for dart in range(12)))
        )
    need(
        [len(cycles) for cycles in boundaries] == [3, 1],
        "planar versus genus-one ribbon boundaries",
    )
    need(
        not all(dart_map[planar[d]] == planar[dart_map[d]] for d in range(12)),
        "J is not planar-ribbon preserving",
    )
    need(
        all(dart_map[interleaved[d]] == interleaved[dart_map[d]] for d in range(12)),
        "J preserves interleaved ribbon",
    )
    planar_inverse = tuple(planar.index(dart) for dart in range(12))
    planar_actions = set()
    for candidate in automorphisms(BOWTIE):
        mapping = candidate.darts(BOWTIE)
        if any(
            all(mapping[planar[d]] == target[mapping[d]] for d in range(12))
            for target in (planar, planar_inverse)
        ):
            planar_actions.add(cycle_action(BOWTIE, candidate))
    need(
        all(matrix_product(action, action) == IDENTITY for action in planar_actions),
        "planar embedding has no H1 quarter-turn even allowing orientation reversal",
    )
    _, chords = cycle_basis(BOWTIE)
    for cycle in boundaries[1]:
        boundary_words.append(
            tuple(
                (1 if dart % 2 == 0 else -1) * (chords.index(dart // 2) + 1)
                for dart in cycle
                if dart // 2 in chords
            )
        )
    word = reduce_word(boundary_words[0])
    need(
        len(word) == 4 and Counter(word) == Counter((1, 2, -1, -2)),
        "filled genus-one boundary adds a commutator relation",
    )
    return {
        "planar_boundary_components": 3,
        "interleaved_boundary_components": 1,
        "thickening_genera": [0, 1],
        "interleaved_boundary_after_tree_collapse": word,
        "planar_allowed_H1_actions": len(planar_actions),
    }


def reduce_word(word: Vector) -> Vector:
    result: list[int] = []
    for letter in word:
        if abs(letter) not in (1, 2):
            raise ValueError("two reversible cycle generators required")
        if result and result[-1] == -letter:
            result.pop()
        else:
            result.append(letter)
    return tuple(result)


def net(word: Vector) -> tuple[int, int]:
    return word.count(1) - word.count(-1), word.count(2) - word.count(-2)


def turn(word: Vector) -> Vector:
    mapping = {1: 2, 2: -1, -1: -2, -2: 1}
    return tuple(mapping[letter] for letter in word)


def history_weight(word: Vector) -> int:
    a, b = net(word)
    return (1 + len(reduce_word(word)) ** 2) * (a * a + b * b)


def path_controls() -> dict[str, object]:
    commutator, spur_reference = (1, 2, -1, -2), (1, -1, 2, -2)
    need(
        Counter(commutator) == Counter(spur_reference),
        "matched oriented cycle and graph-edge counts",
    )
    need(
        reduce_word(commutator) == commutator and reduce_word(spur_reference) == (),
        "free-group history differs despite zero net flow",
    )
    need(
        net(commutator) == net(spur_reference) == (0, 0),
        "abelianization erases commutator",
    )
    need(
        history_weight(commutator) == history_weight(spur_reference) == 0,
        "both words dark in toy history readout",
    )
    continued = (
        history_weight(commutator + (1,)),
        history_weight(spur_reference + (1,)),
    )
    need(continued == (26, 2), "same appended context reveals non-neutral history")
    checked = 0
    for length in range(7):
        for word in product((1, 2, -1, -2), repeat=length):
            rotated = turn(word)
            a, b = net(word)
            need(
                net(rotated) == (-b, a),
                "geometric rotation induces J after abelianization",
            )
            need(
                turn(turn(turn(turn(word)))) == word,
                "order four before abelianization too",
            )
            need(
                reduce_word(rotated) == turn(reduce_word(word)),
                "spur reduction is transport-compatible",
            )
            need(
                history_weight(rotated) == history_weight(word),
                "hidden history readout has C4 covariance",
            )
            need(
                reduce_word(word + (1, -1)) == reduce_word(word),
                "spur neutrality in arbitrary sampled context",
            )
            checked += 1
    return {
        "finite_walks_checked": checked,
        "commutator": commutator,
        "matched_spur_reference": spur_reference,
        "same_context_weights": continued,
        "scope": "free reversible graph histories versus additional abelianization; toy readout, no observed data",
    }


def audit() -> dict[str, object]:
    return {
        "ok": True,
        "simple_graph_census": simple_census(),
        "symmetry": symmetry_controls(),
        "ribbon": ribbon_controls(),
        "paths": path_controls(),
        "boundary": "graph-induced quarter-turn hit; additive homology neutrality, physical norm and readout remain additional premises",
    }


class CycleCarrierTests(unittest.TestCase):
    def test_simple_minimality(self) -> None:
        census = simple_census()
        self.assertEqual([row["whole_H1_J_types"] for row in census], [0, 0, 0, 0, 1])

    def test_graph_symmetry_and_orientation(self) -> None:
        self.assertEqual(symmetry_controls()["bowtie_automorphisms"], 8)

    def test_planar_ribbon_control(self) -> None:
        self.assertEqual(ribbon_controls()["thickening_genera"], [0, 1])

    def test_free_group_countermodel(self) -> None:
        self.assertEqual(path_controls()["same_context_weights"], (26, 2))

    def test_multigraph_is_not_simple_tree(self) -> None:
        collapsed = Graph(3, tuple(sorted(set(MULTI.edges))))
        self.assertEqual(len(collapsed.edges) - collapsed.vertices + 1, 0)


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    parser.add_argument("--json", action="store_true")
    args = parser.parse_args()
    result = audit()
    if args.json:
        print(json.dumps(result, indent=2))
    else:
        print(
            "PASS: 3-vertex/4-edge multigraph and minimal 5-vertex/6-edge simple graph induce J on all H1."
        )
        print(
            "PASS: no canonical J under full graph symmetry; planar and directed-orientation controls."
        )
        print(
            "PASS: equal-count commutator and spur paths separate free histories from additive net flow."
        )
        print(result["boundary"])


if __name__ == "__main__":
    main()
