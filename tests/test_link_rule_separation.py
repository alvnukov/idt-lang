"""Certify exact menu discrimination, never identification outside this menu."""

import json
import subprocess
import sys
import unittest
from collections import Counter
from itertools import combinations

from scripts import probe_link_rule_separation as probe
from scripts.probe_loopless_link_quartet import LooplessGraph


class LinkRuleSeparationTests(unittest.TestCase):
    result: probe.Experiment

    @classmethod
    def setUpClass(cls) -> None:
        cls.result = probe.experiment()

    def test_all_features_attained_and_readouts_agree_with_graph_rule(self) -> None:
        result = self.result
        self.assertEqual(
            result["observable_classes_by_size"], {3: 8, 4: 25, 5: 27, 6: 28}
        )
        self.assertEqual(len(result["preparations"]), 12)
        for prep in result["preparations"]:
            n, state = prep["vertices"], prep["edge_mask"]
            self.assertFalse(state & 1)
            graph = LooplessGraph(n)
            edges = [edge for i, edge in enumerate(graph.edges) if state & (1 << i)]
            p, q = (int(any(k in e for e in edges)) for k in (0, 1))
            occ = 4 if p != q else 2 if p else 1
            self.assertEqual(occ, prep["feature"][1])
            for radius in (None, 2, 3):
                for code in range(8):
                    for initial in (state, state | 1):
                        actual = graph.offer(initial, 0, code, radius) != initial
                        self.assertEqual(
                            actual,
                            probe.predict(("parity", code, radius), prep["feature"]),
                        )

    def test_minima_fixed_and_preserved_aliases(self) -> None:
        result = self.result
        groups = result["aliases"].values()
        self.assertEqual(Counter(map(len, groups)), {1: 24, 2: 1, 5: 2, 12: 1})
        self.assertEqual(len({label for group in groups for label in group}), 48)
        clean = result["fixed_clean"]
        self.assertEqual(clean["optimal_panels"], [(0, 1, 2, 5, 6, 7, 8, 9, 11)])
        robust = result["fixed_one_error"]
        self.assertEqual(robust["cost"], 27)
        self.assertEqual(robust["forced_triplets"], [0, 1, 2, 5, 6, 7, 8, 9])
        self.assertEqual(robust["extra_disjoint_differences"], [[4, 11], [10, 11]])
        for a, b in combinations(result["aliases"], 2):
            distance = sum(((a ^ b) >> i) & 1 for i in robust["panel"])
            self.assertGreaterEqual(distance, 3)

    def test_independent_raw_graph_feature_index(self) -> None:
        # Independent path test: common neighbor, or one edge between the
        # two endpoint neighborhoods. Never reuse the production expansion.
        for n in range(3, 7):
            edges = tuple(combinations(range(n), 2))
            witnesses: dict[probe.Feature, int] = {}
            for mask in range(0, 1 << len(edges), 2):
                links = {e for i, e in enumerate(edges) if mask >> i & 1}
                left = {v for u, v in links if u == 0}
                right = {v for u, v in links if u == 1}
                two = bool(left & right)
                three = any(
                    (u in left and v in right) or (v in left and u in right)
                    for u, v in links
                )
                counts = len(left), len(right)
                par = sorted(c % 2 for c in counts)
                occ = sorted(int(c > 0) for c in counts)
                par_bit = {(0, 0): 1, (0, 1): 4, (1, 1): 2}[par[0], par[1]]
                occ_bit = {(0, 0): 1, (0, 1): 4, (1, 1): 2}[occ[0], occ[1]]
                feature = par_bit, occ_bit, 2 if two else 3 if three else 4
                witnesses.setdefault(feature, mask)
            self.assertEqual(probe.preparations(n), witnesses)

    def test_exhaustive_adaptive_replay_and_lower_bounds(self) -> None:
        result = self.result
        for run, errors in (
            (result["adaptive_clean"], 0),
            (result["adaptive_one_error"], 1),
        ):
            self.assertEqual(run["feasible_depths"][-1], (run["cost"], True))
            self.assertTrue(all(not yes for _, yes in run["feasible_depths"][:-1]))
            self.assertEqual(run["replay"]["clean"], 28)
            self.assertEqual(run["replay"]["worst"], run["cost"])
            for signature in result["aliases"]:
                frontier = [(run["tree"], 0)]
                while frontier:
                    tree, spent = frontier.pop()
                    if tree["kind"] == "end":
                        self.assertEqual(tree["signature"], signature)
                        continue
                    answer = signature >> tree["feature"] & 1
                    frontier.append((tree["children"][answer], spent))
                    if spent < errors:
                        frontier.append((tree["children"][1 - answer], spent + 1))
        self.assertEqual(result["adaptive_clean"]["cost"], 5)
        self.assertEqual(result["adaptive_one_error"]["cost"], 11)
        self.assertGreaterEqual(result["adaptive_one_error"]["replay"]["one_wrong"], 28)

    def test_unmodeled_or_bad_budget_not_conflated_with_identification(self) -> None:
        result = self.result
        panel = result["fixed_one_error"]["panel"]
        words = {tuple(s >> i & 1 for i in panel) for s in result["aliases"]}
        for s in result["aliases"]:
            bits = tuple(s >> i & 1 for i in panel)
            for j in range(len(bits)):
                wrong = bits[:j] + (1 - bits[j],) + bits[j + 1 :]
                self.assertEqual(probe.decode(panel, wrong, result["aliases"], 1), [s])
        word = tuple(j % 2 for j in range(len(panel)))
        self.assertNotIn(word, words)
        self.assertEqual(probe.decode(panel, word, result["aliases"], 1), [])
        self.assertTrue(result["out_of_menu_not_excluded"])
        for bad in ([1] * (len(panel) - 1), [2] * len(panel)):
            with self.assertRaises(ValueError):
                probe.decode(panel, bad, result["aliases"], 1)

    def test_independent_adaptive_last_bit_lower_certificate(self) -> None:
        cert = self.result["adaptive_one_error_lower_certificate"]
        base, rivals = cert["base_signature"], cert["rival_signatures"]
        self.assertIn(base, self.result["aliases"])
        self.assertEqual(len(rivals), 5)
        for r in rivals:
            self.assertNotEqual(r, base)
            self.assertIn(r, self.result["aliases"])
        self.assertTrue(
            all(not ((a ^ base) & (b ^ base)) for a, b in combinations(rivals, 2))
        )
        self.assertEqual(2 * len(rivals) + 1, self.result["adaptive_one_error"]["cost"])

    def test_follow_reports_next_raw_mask_and_retains_every_alias(self) -> None:
        result = self.result
        for budget in (0, 1):
            path = ""
            while True:
                state = probe.follow(result, path, budget, fixed=False)
                self.assertTrue(state["out_of_menu_not_excluded"])
                if state["status"] != "awaiting_toggle":
                    break
                i = state["next_feature"]
                self.assertIsNotNone(i)
                if i is None:
                    self.fail("a waiting state needs a preparation")
                self.assertEqual(state["next_preparation"], result["preparations"][i])
                path += "1" if budget and not path else "0"
            self.assertEqual(state["compatible_labels"], result["aliases"][0])
            self.assertEqual(state["status"], "compatible_submitted_class")
            with self.assertRaises(ValueError):
                probe.follow(result, path + "0", budget, fixed=False)
        impossible = "01" * 13 + "0"
        outside = probe.follow(result, impossible, 1, fixed=True)
        self.assertTrue(outside["out_of_menu_not_excluded"])
        self.assertEqual(outside["status"], "no_compatible_submitted_class")
        with self.assertRaises(ValueError):
            probe.follow(result, "unknown", 1, fixed=True)
        cli = subprocess.run(
            [
                sys.executable,
                "-m",
                "scripts.probe_link_rule_separation",
                "--answers",
                "",
            ],
            check=True,
            capture_output=True,
            text=True,
        )
        self.assertEqual(json.loads(cli.stdout)["status"], "awaiting_toggle")
