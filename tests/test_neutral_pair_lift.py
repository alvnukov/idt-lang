import unittest
from importlib.util import find_spec
from itertools import combinations_with_replacement


class NeutralPairLiftTests(unittest.TestCase):
    def setUp(self):
        name = "scripts.probe_neutral_pair_lift"
        self.assertIsNotNone(find_spec(name), "neutral-pair probe is not implemented")
        from scripts import probe_neutral_pair_lift
        self.p = probe_neutral_pair_lift

    def test_base_pair_forgets_relative_sheet_even_after_renaming(self):
        from scripts.probe_marked_carrier_charge import anonymous_fixture
        graph = anonymous_fixture()
        root = min(graph)
        mark = min(graph.keys() - graph[root] - {root})
        rename = {v: 5009 - 13*i for i, v in enumerate(sorted(graph))}
        other = {rename[v]: frozenset(rename[w] for w in row) for v, row in graph.items()}
        for g, r, m in [(graph, root, mark), (other, rename[root], rename[mark])]:
            audit = self.p.pair_audit(g, r, m)
            self.assertEqual((audit["pairs"], audit["q_neutral"], audit["mixed_x_zero"]), (528, 62, 60))
            self.assertEqual(audit["same_sheet_exceptions"], [((0, 0), 6), ((31, 31), -6)])
            self.assertEqual(audit["projected_root_pair"], (r, r))
            self.assertEqual(audit["global_deck_orbit_sizes"], [2, 1])
            self.assertEqual(audit["independent_deck_orbit_size"], 3)
        with self.assertRaises(ValueError):
            self.p.pair_audit(graph, root, min(graph[root]))

    def test_actual_collision_menu_and_complement(self):
        result = self.p.probe()
        self.assertEqual(result["collision"]["even_unary_binary_counts"], [160, 2560])
        self.assertEqual(result["collision"]["even_ternary_directed_deltas"], {-12: 6, 12: 6})
        self.assertEqual(result["collision"]["example_forward"], [(0, 0, 9), (23, 30, 30), -12])
        self.assertEqual(result["congruence"]["one_packet_checks"], 32)
        self.assertEqual(result["dictionary"]["even_X"], [1, -1, -1, -3, 3, 3])

    def test_creation_controls_are_involutions_on_true_empty_and_all_pairs(self):
        configurations = [(), (0,), (31,), *combinations_with_replacement(range(32), 2)]
        for relation, ref, created in [("opposite", None, (0, 31)), ("same", 0, (0, 0)),
                                       ("same", 1, (31, 31))]:
            step = lambda s: self.p.control_step(s, relation, ref)
            self.assertEqual(step(()), created)
            for s in configurations:
                self.assertEqual(step(step(s)), s)
                expected = () if s == created else created if not s else s
                self.assertEqual(step(s), expected)
                flipped_ref = None if ref is None else 1-ref
                self.assertEqual(self.p.deck(step(s)), self.p.control_step(self.p.deck(s), relation, flipped_ref))
        for rel, ref in [(None, None), ("same", None), ("same", 2), ("unknown", 0)]:
            with self.assertRaises(ValueError):
                self.p.control_step((), rel, ref)
        audit = self.p.probe()["source"]
        self.assertEqual([(row["created"], row["delta_X"]) for row in audit["controls"]],
                         [((0, 31), 0), ((0, 0), 6), ((31, 31), -6)])
        self.assertEqual(audit["root_pair_fixed_outputs"], [(0, 31)])
        self.assertFalse(audit["native_law_selected"])
