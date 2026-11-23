import unittest
from itertools import pairwise

from scripts import probe_clean_quartet_compiler as probe
from scripts.probe_relational_quartet_records import Graph, Rule, fresh


class CleanQuartetCompilerTests(unittest.TestCase):
    def test_all_fresh_inputs_and_rule_controls(self) -> None:
        graph = Graph.complete(4)
        word = probe.compiled_offers()
        self.assertEqual(len(word), 15)
        self.assertEqual(
            word,
            (
                (0, 1),
                (0, 2),
                (0, 3),
                (2, 3),
                (1, 3),
                (0, 3),
                (0, 1),
                (0, 2),
                (2, 3),
                (1, 3),
                (0, 3),
                (0, 1),
                (1, 3),
                (0, 2),
                (2, 3),
            ),
        )
        for rule, expected_matches in (
            (Rule.GUARDED_SAME_SIGN, 16),
            (Rule.SAME_SIGN, 16),
            (Rule.ZERO_ONLY, 10),
        ):
            matches = 0
            for bits in range(16):
                target = (bits ^ 15, 0) if bits.bit_count() == 2 else (bits, 0)
                trace = probe.replay(graph, (bits, 0), word, rule)
                matches += trace[-1] == target
                if rule is Rule.GUARDED_SAME_SIGN:
                    self.assertEqual(trace[-1], target)
                    changes = sum(a != b for a, b in pairwise(trace))
                    self.assertEqual(changes, (0, 4, 8, 4, 0)[bits.bit_count()])
            self.assertEqual(matches, expected_matches)

    def test_raw_arm_swap_and_relabelled_compiler(self) -> None:
        graph = Graph(4, ((0, 1), (1, 2), (2, 3)))
        before = (fresh("1001")[0], 0b111)
        after = (fresh("0101")[0], 0b111)
        self.assertEqual(probe.raw_offer(graph, before, (0, 1)), after)
        self.assertEqual(probe.raw_offer(graph, after, (1, 0)), before)
        self.assertEqual(probe.raw_offer(graph, before, (0, 2)), before)
        clique = Graph.complete(5)
        permuted = probe.compiled_offers((4, 2, 0, 1))
        self.assertEqual(
            probe.replay(clique, fresh("01001"), permuted)[-1], fresh("10100")
        )

    def test_direct_reach_is_not_a_common_word(self) -> None:
        graph = Graph.complete(4)
        for bits in range(16):
            ends = probe.clean_distances(graph, bits)
            expected = {bits: 0, bits ^ 15: 8} if bits.bit_count() == 2 else {bits: 0}
            self.assertEqual(ends, expected)
        bare = probe.bare_path_control()
        self.assertEqual(bare.single_input_minimum, 8)
        self.assertFalse(bare.common_word_exists)
        self.assertEqual(bare.product_reachable_states, 12)

    def test_bare_path_witness_and_incompatible_01_offer_parities(self) -> None:
        bare = probe.bare_path_control()
        path = Graph(4, ((0, 1), (1, 2), (2, 3)))
        self.assertEqual(bare.parity_pair, (0, 1))
        self.assertEqual(bare.parities_to_changed, (1,))
        self.assertEqual(bare.parities_to_fixed, (0,))
        self.assertEqual(len(bare.single_input_word), 8)
        self.assertEqual(
            probe.replay(path, fresh("0110"), bare.single_input_word)[-1], fresh("1001")
        )
        self.assertEqual(
            probe.replay(path, fresh("1001"), bare.single_input_word)[-1], fresh("0110")
        )
        self.assertNotEqual(
            probe.replay(path, fresh("1000"), bare.single_input_word)[-1], fresh("1000")
        )

    def test_compiler_word_is_shortest_in_serial_pair_offers(self) -> None:
        result = probe.shortest_compiler_certificate()
        self.assertEqual(result.minimum_offers, 15)
        self.assertEqual(result.representative_inputs, (1, 2, 3, 4, 5, 6, 7))
        layers = (1, 6, 27, 96, 372, 1496, 5480, 18890)
        self.assertEqual(result.forward_layers, layers)
        self.assertEqual(result.backward_layers, layers)
        self.assertEqual(result.depth_7_overlap, 0)

    def test_sparse_raw_clean_reach_and_path_macro_agree_small_graphs(self) -> None:
        for size, expected in enumerate(
            (
                (1, 1, 1, 0),
                (1, 2, 2, 0),
                (2, 8, 10, 0),
                (8, 64, 112, 0),
                (64, 1024, 3136, 126),
                (1024, 32768, 206848, 12300),
            )
        ):
            with self.subTest(size=size):
                result = probe.opportunity_census(size)
                self.assertEqual(
                    (
                        result.graphs,
                        result.graph_inputs,
                        result.raw_states,
                        result.nontrivial_graph_inputs,
                    ),
                    expected,
                )

    def test_exterior_can_change_gate_even_when_exterior_is_restored(self) -> None:
        result = probe.disturbance_control()
        self.assertTrue(result.both_injections_effective)
        self.assertEqual(result.undisturbed_output, "10010")
        self.assertEqual(result.disturbed_output, "01100")
        self.assertEqual(result.disturbed_final_bonds, 0)
        self.assertTrue(result.exterior_restored)
        self.assertEqual(result.interrupt_after_offers, 12)


if __name__ == "__main__":
    unittest.main()
