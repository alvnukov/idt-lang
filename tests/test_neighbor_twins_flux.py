"""Finite behavior checks for the neighboring-shell twins probe."""

import json
import subprocess
import sys
import unittest
from pathlib import Path

from scripts.probe_neighbor_twins_flux import (
    K5,
    OCTAHEDRON,
    RULES,
    Edge,
    Incidence,
    Rule,
    local_result,
    mask_of,
)

SCRIPT = (
    Path(__file__).resolve().parents[1] / "scripts" / "probe_neighbor_twins_flux.py"
)


def reference_event(
    edges: tuple[Edge, ...],
    occupied: frozenset[Edge],
    center: int,
    rule: Rule,
) -> frozenset[Edge] | None:
    """Literal occupied-edge sets, independent of bit positions and shell masks."""
    star = {edge for edge in edges if center in edge}
    if len(star & occupied) != 2:
        return None
    outside = occupied - star
    scores = {
        edge: sum((set(edge) - {center}).issubset(e) for e in outside) for edge in star
    }
    pairs = {
        (edge, twin)
        for edge in star
        for twin in star
        if edge != twin
        and scores[edge] == scores[twin]
        and sum(score == scores[edge] for score in scores.values()) == 2
    }
    covered = {a for a, _ in pairs}
    singles = {
        edge
        for edge in star - covered
        if list(scores.values()).count(scores[edge]) == 1
    }
    if rule == "F" and len(singles) == 2:
        a, b = sorted(singles)
        pairs.update({(a, b), (b, a)})
    changed = {a for a, b in pairs if (a in occupied) != (b in occupied)}
    return occupied.symmetric_difference(changed) if changed else None


class NeighborTwinsFluxTest(unittest.TestCase):
    def test_probe_distinguishes_local_offers_from_reachable_flux(self) -> None:
        process = subprocess.run(
            [sys.executable, "-B", str(SCRIPT)],
            cwd=SCRIPT.parent.parent,
            capture_output=True,
            text=True,
            check=False,
        )
        self.assertEqual(process.returncode, 0, process.stderr)
        report = json.loads(process.stdout)

        local = report["local"]
        self.assertEqual(local["score_bit_inputs"], 4096)
        self.assertEqual(local["enabled_disagreements"], 0)
        self.assertEqual(local["f_nonstar_events"], 0)
        self.assertEqual(local["irreversibilities"], 0)

        k5 = report["K5"]
        self.assertEqual(k5["state_count"], 252)
        self.assertEqual(k5["moving_states"], 120)
        self.assertEqual(k5["triangle_count"], 10)
        self.assertEqual(k5["enabled_disagreements"], 0)
        self.assertEqual(k5["output_disagreements"], 0)
        self.assertEqual(k5["T"]["component_histogram"], {"1": 132, "6": 20})
        self.assertEqual(k5["T"]["six_cycle_components"], 20)
        self.assertEqual(k5["T"]["triangle_changing_events"], 0)
        self.assertEqual(k5["T"], k5["F"])
        ring = k5["return_example"]
        self.assertEqual(ring["backtrack_centers"], [2, 2])
        self.assertEqual(ring["nonbacktracking_centers"], [2, 0, 3, 2, 0, 3])
        self.assertFalse(ring["direction_is_supplied_by_local_rule"])

        octahedron = report["octahedron"]
        self.assertEqual(octahedron["state_count"], 924)
        self.assertEqual(octahedron["moving_states"], 600)
        self.assertEqual(octahedron["triangle_count"], 8)
        self.assertEqual(octahedron["enabled_disagreements"], 0)
        t_report = octahedron["T"]
        f_report = octahedron["F"]
        self.assertEqual(t_report["nontrivial_events"], 864)
        self.assertEqual(f_report["nontrivial_events"], 864)
        self.assertEqual(t_report["triangle_change_histogram"], {"0": 480, "2": 384})
        self.assertEqual(t_report["triangle_changing_events"], 384)
        self.assertEqual(f_report["triangle_changing_events"], 0)
        self.assertEqual(
            t_report["changed_odd_count_pairs"],
            {
                "2->4": 96,
                "4->2": 96,
                "4->6": 96,
                "6->4": 96,
            },
        )
        self.assertEqual(t_report["two_odd_starts"], 168)
        self.assertEqual(t_report["relocatable_two_odd_starts"], 0)
        self.assertEqual(t_report["two_odd_starts_reaching_six_odd"], 0)
        shortest = octahedron["four_to_four_example"]
        self.assertEqual(
            shortest["initial_occupied_edges"],
            [
                [0, 2],
                [0, 3],
                [0, 4],
                [0, 5],
                [1, 3],
                [2, 4],
            ],
        )
        self.assertEqual(shortest["T_shortest_centers"], [4, 3])
        self.assertEqual(
            shortest["T_odd_triangles"],
            [
                [[0, 2, 4], [1, 2, 4], [1, 3, 4], [1, 3, 5]],
                [[1, 2, 4], [1, 3, 5]],
                [[0, 3, 5], [1, 2, 4], [1, 3, 4], [1, 3, 5]],
            ],
        )
        self.assertIsNone(shortest["F_shortest_centers"])
        self.assertEqual(shortest["F_first_null_center_in_T_word"], 3)

    def test_score_relabeling_and_port_permutation(self) -> None:
        scores = (0, 0, 1, 3)
        marks = (1, 0, 1, 0)
        order = (2, 0, 3, 1)
        relabel_score = {0: 19, 1: -6, 3: 2}
        self.assertEqual(local_result(scores, marks, "T"), (0, 1, 1, 0))
        self.assertEqual(local_result(scores, marks, "F"), (0, 1, 0, 1))
        for rule in RULES:
            expected = local_result(scores, marks, rule)
            self.assertEqual(
                local_result(
                    tuple(relabel_score[scores[p]] for p in order),
                    tuple(marks[p] for p in order),
                    rule,
                ),
                tuple(expected[p] for p in order),
            )
            self.assertEqual(local_result(scores, (1, 0, 0, 0), rule), (1, 0, 0, 0))
        self.assertEqual(local_result(scores, (1, 1, 0, 0), "T"), (1, 1, 0, 0))
        self.assertEqual(local_result(scores, (1, 1, 0, 0), "F"), (1, 1, 0, 0))

    def test_literal_events_and_nontrivial_graph_relabeling(self) -> None:
        graphs = ((K5, (2, 4, 0, 1, 3)), (OCTAHEDRON, (1, 4, 0, 2, 5, 3)))
        for graph, label in graphs:
            by_old_index = tuple(
                (min(label[a], label[b]), max(label[a], label[b]))
                for a, b in graph.edges
            )
            renamed = Incidence.build(len(label), by_old_index)
            new_indices = tuple(renamed.edges.index(edge) for edge in by_old_index)
            edge_count = len(graph.edges)
            state_map = {
                state: mask_of(
                    tuple(new_indices[i] for i in range(edge_count) if state & (1 << i))
                )
                for state in graph.half_filled()
            }
            edge_sets = {
                state: frozenset(graph.occupied_edges(state)) for state in state_map
            }
            for state, occupied in edge_sets.items():
                self.assertEqual(
                    set(renamed.odd_triangles(state_map[state])),
                    {
                        tuple(sorted(label[v] for v in cycle))
                        for cycle in graph.odd_triangles(state)
                    },
                )
                for center in range(len(label)):
                    for rule in RULES:
                        result = graph.event(state, center, rule)
                        reference = reference_event(graph.edges, occupied, center, rule)
                        self.assertEqual(
                            None if result is None else edge_sets[result], reference
                        )
                        self.assertEqual(
                            renamed.event(state_map[state], label[center], rule),
                            None if result is None else state_map[result],
                        )
                        if result is not None:
                            self.assertEqual(graph.event(result, center, rule), state)

    def test_ring_closes_without_making_inverse_unavailable(self) -> None:
        initial: frozenset[Edge] = frozenset({(0, 2), (0, 3), (0, 4), (1, 2), (1, 3)})
        current = initial
        first = reference_event(K5.edges, initial, 2, "T")
        self.assertIsNotNone(first)
        if first is not None:
            self.assertEqual(reference_event(K5.edges, first, 2, "T"), initial)
        for center in (2, 0, 3, 2, 0, 3):
            next_state = reference_event(K5.edges, current, center, "T")
            if next_state is None:
                self.fail(f"center {center} missing from ring")
            current = next_state
        self.assertEqual(current, initial)


if __name__ == "__main__":
    unittest.main()
