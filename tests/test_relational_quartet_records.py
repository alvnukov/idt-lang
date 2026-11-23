import json
import subprocess
import sys
import unittest
from pathlib import Path

from scripts.probe_relational_quartet_records import (
    Graph,
    Rule,
    balanced_census,
    fresh,
    opportunity_census,
    pair_fair_word,
    reachable,
    replay,
    symmetric_controls,
)


class RelationalQuartetRecordsTests(unittest.TestCase):
    def test_complete_graph_reachability_and_shortest_offers(self) -> None:
        for size, states, positive, double, words in (
            (4, 9, 2, 0, 4),
            (6, 70, 36, 0, 36),
            (8, 785, 576, 72, 144),
        ):
            with self.subTest(size=size):
                census = balanced_census(size, Rule.ZERO_ONLY)
                self.assertEqual(census["reachable_states"], states)
                self.assertEqual(census["states_with_record"], positive)
                self.assertEqual(census["states_with_two_records"], double)
                self.assertEqual(census["minimum_offers_to_record"], 3)
                self.assertEqual(census["shortest_ordered_offer_words"], words)
                self.assertEqual(
                    census["shape_depth_and_multiplicities_checked_states"], states
                )

    def test_bridge_certifies_own_quartet_but_not_exclusive_completion(self) -> None:
        graph = Graph.complete(6)
        start = fresh("011001")
        word = ((0, 1), (2, 3), (4, 5), (1, 2))
        reached = replay(graph, start, word, Rule.ZERO_ONLY)[-1]
        records = graph.records(reached, Rule.ZERO_ONLY)
        self.assertEqual(records, (((1, 2), (0, 1, 2, 3)),))
        self.assertEqual(reached[0] ^ start[0], 0b111111)
        restored = graph.offer(reached, (2, 1), Rule.ZERO_ONLY)
        self.assertEqual(restored, replay(graph, start, word[:-1], Rule.ZERO_ONLY)[-1])
        self.assertEqual(graph.records(restored, Rule.ZERO_ONLY), ())
        self.assertEqual(restored[0] ^ start[0], 0b111111)

    def test_fixed_offer_involution_and_locality_on_literal_reachable_graph(
        self,
    ) -> None:
        graph = Graph.complete(6)
        start = fresh("000111")
        for rule in (Rule.ZERO_ONLY, Rule.SAME_SIGN, Rule.GUARDED_SAME_SIGN):
            for before in reachable(graph, start, rule):
                for i, (a, b) in enumerate(graph.edges):
                    after = graph.offer(before, (a, b), rule)
                    self.assertEqual(graph.offer(after, (a, b), rule), before)
                    self.assertEqual(graph.offer(before, (b, a), rule), after)
                    self.assertIn(before[0] ^ after[0], (0, (1 << a) | (1 << b)))
                    self.assertIn(before[1] ^ after[1], (0, 1 << i))

    def test_pair_fair_lasso_never_records_on_a_graph_that_can_record(self) -> None:
        # The closing opportunity chord is allowed; the criterion is not induced.
        graph = Graph(4, ((0, 1), (0, 3), (1, 2), (2, 3)))
        start = fresh("0110")
        trace = replay(graph, start, pair_fair_word(graph), Rule.ZERO_ONLY)
        self.assertEqual(trace[-1], start)
        self.assertFalse(any(graph.records(s, Rule.ZERO_ONLY) for s in trace))
        self.assertTrue(
            any(graph.records(s, Rule.ZERO_ONLY) for s in reachable(graph, start))
        )
        self.assertEqual(graph.offer(start, (0, 2)), start)  # not an opportunity

    def test_every_four_and_five_site_graph_and_word_against_path_criterion(
        self,
    ) -> None:
        self.assertEqual(
            opportunity_census(4),
            {"sites": 4, "graph_word_pairs": 1024, "admitting_pairs": 84},
        )
        self.assertEqual(
            opportunity_census(5),
            {"sites": 5, "graph_word_pairs": 32768, "admitting_pairs": 8620},
        )

    def test_positive_asymmetry_cannot_just_be_removed(self) -> None:
        controls = symmetric_controls()
        self.assertEqual(controls["cycle_four"]["naive_final_degrees"], (2, 2, 2, 2))
        self.assertEqual(
            controls["path_six"]["naive_final_degrees"], (1, 2, 2, 2, 2, 1)
        )
        for row in controls.values():
            self.assertTrue(row["naive_all_offers_change_state"])
            self.assertTrue(row["guard_refuses_final_offer"])
        for size, count in ((4, 11), (6, 106), (8, 1505)):
            with self.subTest(size=size):
                census = balanced_census(size, Rule.GUARDED_SAME_SIGN)
                self.assertEqual(census["reachable_states"], count)
                self.assertEqual(
                    census["shape_depth_and_multiplicities_checked_states"], count
                )

    def test_cli_is_sorted_json_in_optimized_mode(self) -> None:
        script = (
            Path(__file__).resolve().parents[1]
            / "scripts"
            / ("probe_relational_quartet_records.py")
        )
        completed = subprocess.run(
            [sys.executable, "-O", str(script)],
            check=True,
            capture_output=True,
            text=True,
        )
        report = json.loads(completed.stdout)
        self.assertEqual(
            completed.stdout, json.dumps(report, indent=2, sort_keys=True) + "\n"
        )
        self.assertEqual(report["opportunity_graphs"][-1]["admitting_pairs"], 8620)
        self.assertTrue(report["scope"]["positive_asymmetry_supplied"])
        self.assertFalse(report["scope"]["irreversible_event"])


if __name__ == "__main__":
    unittest.main()
