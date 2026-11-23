"""Full-state controls for addressed matching-port words on loopless graphs."""

import json
import subprocess
import sys
import unittest

from scripts import probe_loopless_matching_ports as probe
from scripts.probe_loopless_link_quartet import (
    BLANK_NAND,
    BLANK_OR,
    Edge,
    LooplessGraph,
)


def _mask(graph: LooplessGraph, *bonds: Edge) -> int:
    return sum(1 << graph.edge_index[(min(a, b), max(a, b))] for a, b in bonds)


class LooplessMatchingPortsTest(unittest.TestCase):
    def test_cnot_preserves_all_disjoint_spectator_bonds(self) -> None:
        graph = LooplessGraph(10)
        control, target = (5, 2), (9, 0)
        triangle = ((1, 3), (1, 4), (3, 4))
        word = probe.addresses(graph, probe.cnot_word(control, target))
        self.assertEqual(len(word), 7)
        for controls in range(4):
            present = tuple(
                edge for i, edge in enumerate((control, target)) if controls >> i & 1
            )
            for bits in range(8):
                external = tuple(
                    edge for i, edge in enumerate(triangle) if bits >> i & 1
                )
                start = _mask(graph, *present, *external)
                expected = start ^ (_mask(graph, target) if controls & 1 else 0)
                self.assertEqual(graph.replay(start, word, 6), expected)

    def test_parity_copy_records_only_source_parity_and_restores_bridges(self) -> None:
        graph = LooplessGraph(6)
        source_bonds = tuple(edge for edge in graph.edges if max(edge) < 4)
        scratch = (5, 4)
        anchor = 2
        word = probe.addresses(graph, probe.parity_copy_word(anchor, scratch))
        self.assertEqual(len(word), 3)
        for bits in range(64):
            bonds = tuple(edge for i, edge in enumerate(source_bonds) if bits >> i & 1)
            start = _mask(graph, *bonds)
            expected = start | (
                _mask(graph, scratch)
                if sum(anchor in edge for edge in bonds) % 2
                else 0
            )
            self.assertEqual(graph.replay(start, word, 6), expected)
            self.assertEqual(graph.replay(expected, word[::-1], 6), start)

    def test_toffoli_is_clean_and_missing_reset_disturbs_next_gate(self) -> None:
        graph = LooplessGraph(8)
        x, y, target, scratch = (0, 1), (2, 3), (4, 5), (6, 7)
        word = probe.addresses(graph, probe.toffoli_word(x, y, target, scratch))
        self.assertEqual(len(word), 22)
        dirty_target_inputs = []
        wrong_after_skipping_reset = []
        for bits in range(8):
            start = _mask(
                graph,
                *(edge for i, edge in enumerate((x, y, target)) if bits >> i & 1),
            )
            target_bit = _mask(graph, target)
            expected = start ^ (target_bit if (bits & 3) == 3 else 0)
            clean = graph.replay(start, word, 6)
            self.assertEqual(clean, expected)
            self.assertEqual(graph.replay(clean, word, 6), start)
            dirty = graph.replay(start | _mask(graph, scratch), word, 6)
            if (dirty ^ expected) & target_bit:
                dirty_target_inputs.append(bits)
            no_reset = graph.replay(start, word[:11] + word[14:], 6)
            if (graph.replay(no_reset, word, 6) ^ start) & target_bit:
                wrong_after_skipping_reset.append(bits)
        self.assertEqual(len(dirty_target_inputs), 2)
        self.assertEqual(wrong_after_skipping_reset, [2, 6])

    def test_quartet_complete_word_and_flag_on_all_inputs(self) -> None:
        graph = LooplessGraph(14)
        data = ((3, 2), (5, 4), (7, 6), (1, 0))
        temporary, flag, scratch = (10, 11), (13, 12), (8, 9)
        program = probe.quartet_program(data, temporary, flag, scratch)
        self.assertEqual(
            (len(program.select), len(program.toggle), len(program.word)),
            (396, 28, 820),
        )
        select = probe.addresses(graph, program.select)
        toggle = probe.addresses(graph, program.toggle)
        word = probe.addresses(graph, program.word)
        block = _mask(graph, *data)
        for bits in range(16):
            start = _mask(
                graph, *(edge for i, edge in enumerate(data) if bits >> i & 1)
            )
            selected = bits.bit_count() == 2
            flag_bit = _mask(graph, flag) if selected else 0
            target = start ^ block if selected else start
            self.assertEqual(graph.replay(start, select, 6), start | flag_bit)
            self.assertEqual(graph.replay(start, select + toggle, 6), target | flag_bit)
            self.assertEqual(graph.replay(start, word, 6), target)

    def test_shared_matching_port_composition_checks_both_orderings(self) -> None:
        left, right = probe.audit_shared_port_composition()
        self.assertEqual(
            (left.order, right.order), ("left_then_right", "right_then_left")
        )
        for row in (left, right):
            self.assertEqual((row.logical_inputs, row.spectator_states), (128, 2))
            self.assertEqual((row.clean_through, row.final_matches), (256, 256))
            self.assertEqual(row.logical_order_differences, 54)

    def test_literal_glue_scans_all_roles_alignments_and_inputs(self) -> None:
        or_row = probe.audit_literal_k4_edge_glue(BLANK_OR)
        nand_row = probe.audit_literal_k4_edge_glue(BLANK_NAND)
        for row in (or_row, nand_row):
            self.assertEqual((row.gluing_count, row.inputs_per_gluing), (32, 128))
            self.assertEqual((row.fully_final_gluings, row.fully_clean_gluings), (0, 0))
            self.assertEqual(sum(row.final_matches_histogram.values()), 32)
            self.assertEqual(sum(row.clean_through_matches_histogram.values()), 32)
        self.assertEqual((or_row.code, or_row.word_length), (6, 30))
        self.assertEqual((nand_row.code, nand_row.word_length), (5, 74))
        self.assertEqual((or_row.min_final_matches, or_row.max_final_matches), (18, 57))
        self.assertEqual(
            (nand_row.min_final_matches, nand_row.max_final_matches), (23, 80)
        )
        self.assertEqual(or_row.final_matches_histogram[57], 2)
        self.assertEqual(nand_row.final_matches_histogram[80], 1)
        self.assertEqual(
            or_row.final_matches_histogram, or_row.clean_through_matches_histogram
        )
        self.assertEqual(
            (
                or_row.correct_final_wrong_intermediate,
                nand_row.correct_final_wrong_intermediate,
            ),
            (0, 2),
        )

    def test_port_compilers_reject_shared_vertices_within_one_gate(self) -> None:
        with self.assertRaises(ValueError):
            probe.cnot_word((0, 1), (1, 2))
        with self.assertRaises(ValueError):
            probe.parity_copy_word(0, (1, 0))
        with self.assertRaises(ValueError):
            probe.toffoli_word((0, 1), (2, 3), (4, 5), (3, 6))
        with self.assertRaises(ValueError):
            probe.quartet_program(
                ((0, 1), (2, 3), (4, 5), (6, 7)), (8, 9), (10, 11), (4, 12)
            )


class LooplessMatchingPortsCliTest(unittest.TestCase):
    def test_optimized_probe_retains_full_state_controls(self) -> None:
        result = subprocess.run(
            [sys.executable, "-O", "-m", "scripts.probe_loopless_matching_ports"],
            capture_output=True,
            text=True,
            check=False,
        )
        self.assertEqual(result.returncode, 0, result.stderr)
        report = json.loads(result.stdout)
        self.assertEqual(report["matched_ports"]["quartet_clean_inputs"], 16)
        self.assertEqual(
            report["matched_ports"]["quartet_no_uncompute_dirty_inputs"], 6
        )
        self.assertEqual(
            report["matched_ports"].get("toffoli_no_reset_then_clean_wrong_targets"), 2
        )
        self.assertEqual(
            [row["clean_through"] for row in report["shared_port_composition"]],
            [256, 256],
        )
        self.assertEqual(
            [row["fully_clean_gluings"] for row in report["literal_k4_edge_glue"]],
            [0, 0],
        )
