"""Adversarial outcomes and an exhaustive, history-based small policy oracle."""

import copy
import json
import unittest
from itertools import combinations, product
from unittest.mock import patch

from theory_experiments import discrimination_design as design


def query(name, cost, allows, outcomes=("0", "1")):
    return {"id": name, "cost": cost, "outcomes": list(outcomes), "allows": allows}


def spec(models, *tests):
    return {"schema": design.SCHEMA, "models": list(models), "tests": list(tests)}


def support(test, model):
    x = test["allows"].get(model)
    return set(test["outcomes"] if x is None else x)


def ambiguous(models, tests):
    return {tuple(sorted((a, b))) for a, b in combinations(models, 2)
            if all(support(t, a) & support(t, b) for t in tests)}


def brute(models, remaining, all_tests):
    # Enumerate finite decision trees, INCLUDING tests on which an outcome
    # preserves every survivor. Once a test returned a label, all its survivors
    # allow that same label on every fresh repeat, so a minimax adversary can
    # defeat any subsequent attempt to gain information by repeating it.
    if len(ambiguous(models, all_tests)) == len(models)*(len(models)-1)//2:
        return 0
    best = float("inf")
    for i, t in enumerate(remaining):
        branches = [[m for m in models if label in support(t, m)] for label in t["outcomes"]]
        suffix = remaining[:i]+remaining[i+1:]
        best = min(best, t["cost"]+max(brute(child, suffix, all_tests) for child in branches if child))
    return best


def validate_plan(s, result):
    tests = {t["id"]: t for t in s["tests"]}
    nodes = result["nodes"]
    seen = set()

    def walk(key, models):
        row = nodes[key]
        if row["survivors"] != sorted(models):
            raise AssertionError("incorrect survivor labels")
        if key in seen:
            return row["worst_cost"]
        seen.add(key)
        if row["test"] is None:
            if row["children"] or len(ambiguous(models, s["tests"])) != len(models)*(len(models)-1)//2:
                raise AssertionError("leaf left a robust distinction unresolved")
            value = 0
        else:
            t = tests[row["test"]]
            if set(row["children"]) != set(t["outcomes"]):
                raise AssertionError("missing declared outcome")
            costs = []
            for label, child in row["children"].items():
                left = [m for m in models if label in support(t, m)]
                if left:
                    if len(left) >= len(models) or child is None:
                        raise AssertionError("invalid progress")
                    costs.append(walk(child, left))
                elif child is not None:
                    raise AssertionError("outside-library outcome was promoted into a model")
            value = t["cost"]+max(costs)
        if row["worst_cost"] != value:
            raise AssertionError("wrong additional cost")
        return value

    value = walk(result["root"], s["models"])
    return value == result["worst_cost"] and seen == set(nodes)


class DesignTests(unittest.TestCase):
    def test_adaptive_two_vs_three_nonadaptive_costly_one_shot_and_deterministic_ties(self):
        probe = spec("ABCD", query("split", 1, {"A": ["0"], "B": ["0"], "C": ["1"], "D": ["1"]}),
                     query("left", 1, {m: [str(int(m == "B"))] for m in "ABCD"}),
                     query("right", 1, {m: [str(int(m == "D"))] for m in "ABCD"}),
                     query("direct", 9, {m: [m] for m in "ABCD"}, "ABCD"))
        ans = design.plan_design(probe)
        self.assertEqual((ans["worst_cost"], ans["nodes"][ans["root"]]["test"]), (2, "split"))
        self.assertTrue(validate_plan(probe, ans))
        fixed_min = min(sum(t["cost"] for t in menu) for k in range(1, 5)
                        for menu in combinations(probe["tests"], k) if not ambiguous(probe["models"], menu))
        self.assertEqual(fixed_min, 3)
        tied = spec("AB", query("z", 2, {"A": ["0"], "B": ["1"]}), query("a", 2, {"A": ["1"], "B": ["0"]}))
        out = design.plan_design(tied)
        self.assertEqual(out["nodes"][out["root"]]["test"], "a")
        reordered = copy.deepcopy(tied)
        reordered["models"].reverse()
        reordered["tests"].reverse()
        for t in reordered["tests"]:
            t["outcomes"].reverse()
        self.assertEqual(out, design.plan_design(reordered))

    def test_uncertainty_bridge_is_not_a_transitive_equivalence(self):
        for maybe in ({}, {"B": None}, {"B": ["0", "1"]}):
            probe = spec("CBA", query("read", 3, {"A": ["0"], "C": ["1"], **maybe}))
            answer = design.plan_design(probe)
            self.assertEqual(answer["unseparable_pairs"], [["A", "B"], ["B", "C"]])
            self.assertEqual((answer["root"], answer["worst_cost"]), ("s7", 3))
            node = answer["nodes"][answer["root"]]
            self.assertEqual([answer["nodes"][k]["survivors"] for k in node["children"].values()],
                             [["A", "B"], ["B", "C"]])
            self.assertTrue(validate_plan(probe, answer))
        # All pairs overlap somewhere, yet no outcome covers all three.
        # Identifying a single model is not the objective; do not pay for a
        # shrink-only query if NO pair can be separated in the worst case.
        pairwise = spec("ABC", query("read", 1, {"A": ["x", "y"], "B": ["y", "z"], "C": ["x", "z"]}, "xyz"))
        ans = design.plan_design(pairwise)
        self.assertEqual((ans["worst_cost"], ans["nodes"]["s7"]["test"]), (0, None))
        self.assertEqual(len(ans["unseparable_pairs"]), 3)

    def test_outside_library_and_no_assumption_of_shared_nuisances(self):
        probe = spec("AB", query("contrast", 5, {"A": ["x"], "B": ["y"]}, "xyz"))
        ans = design.plan_design(probe)
        self.assertIsNone(ans["nodes"]["s3"]["children"]["z"])
        self.assertTrue(validate_plan(probe, ans))
        # A purported same-hidden-state correlation between observations is
        # not expressible. Both fresh supports are full in each preparation.
        fresh = spec("AB", query("first", 1, {"A": ["0", "1"]}), query("second", 1, {"B": ["1", "0"]}))
        self.assertEqual(design.plan_design(fresh)["unseparable_pairs"], [["A", "B"]])
        self.assertEqual(design.plan_design(fresh)["worst_cost"], 0)
        for probe in (spec(["alone"]), spec("AB"), spec("AB", query("wild", 1, {}))):
            self.assertEqual(design.plan_design(probe)["worst_cost"], 0)

    def test_against_all_two_binary_query_tables_on_three_models(self):
        choices = [["0"], ["1"], ["0", "1"]]
        choices3 = list(product(choices, repeat=3))
        for first, second in product(choices3, repeat=2):
            tests = [query("first", 2, dict(zip("ABC", first, strict=True))), query("second", 3, dict(zip("ABC", second, strict=True)))]
            s = spec("ABC", *tests)
            ans = design.plan_design(s)
            self.assertEqual(ans["worst_cost"], brute(list("ABC"), tests, tests))
            self.assertTrue(validate_plan(s, ans))

    def test_budgets_are_hard_and_never_publish_an_unearned_plan(self):
        s = spec("AB", query("one", 1, {"A": ["0"], "B": ["1"]}))
        original = copy.deepcopy(s)
        full = design.plan_design(s)
        for limit in range(full["states_examined"]):
            out = design.plan_design(s, state_budget=limit)
            self.assertEqual((out["status"], out["worst_cost"], out["root"], out["nodes"], out["stop_reason"]),
                             ("budget_exhausted", None, None, {}, "state_budget"))
            self.assertEqual((out["states_examined"], out["models"]), (limit, ["A", "B"]))
        self.assertEqual(design.plan_design(s, state_budget=full["states_examined"])["status"], "optimal")
        with patch.object(design, "MAX_POLICY_NODES", 2):
            out = design.plan_design(s)
            self.assertEqual((out["nodes"], out["root"], out["worst_cost"], out["stop_reason"]),
                             ({}, None, None, "policy_node_limit"))
        self.assertEqual(original, s)
        self.assertEqual(json.loads(json.dumps(full)), full)

    def test_shared_children_and_maximum_model_test_and_cost_limits(self):
        shared = spec("ABC", query("read", 1, {"A": ["x", "y"], "B": ["x", "y"], "C": ["z"]}, "xyz"))
        ans = design.plan_design(shared)
        children = ans["nodes"][ans["root"]]["children"]
        self.assertEqual(children["x"], children["y"])
        self.assertEqual(len(ans["nodes"]), 3)
        models = [f"m{i:02}" for i in range(16)]
        tests = [query(f"bit{k}", 10**9, {m: [str((i >> k) & 1)] for i, m in enumerate(models)})
                 for k in range(4)]
        tests += [query(f"wild{i}", 1, {}) for i in range(20)]
        maximal = spec(models, *tests)
        ans = design.plan_design(maximal)
        self.assertEqual((ans["status"], ans["worst_cost"], len(ans["nodes"])), ("optimal", 4*10**9, 31))
        self.assertTrue(validate_plan(maximal, ans))

    def test_schema_rejects_malformed_inputs_without_filtering_models(self):
        t = query("t", 1, {})
        s = spec("AB", t)
        for key, val in (("schema", True), ("schema", "different"), ("models", []), ("models", [True]),
                         ("models", ["A", "A"]), ("models", list("abcdefghijklmnopq")), ("models", [" ö"]),
                         ("models", ["X"*65]), ("models", ["a\nb"]), ("tests", [t]*25), ("tests", [t,t]),
                         ("tests", {}), ("history", [])):
            with self.subTest(key=key), self.assertRaises(ValueError):
                design.plan_design({**s, key: val})
        for key, val in (("id", False), ("id", " t"), ("cost", True), ("cost", 0), ("cost", 1.0), ("cost", 10**9+1),
                         ("outcomes", ["0"]), ("outcomes", ["0","0"]), ("outcomes", ["a","b","c","d","e"]),
                         ("allows", None), ("allows", {"C": None}), ("allows", {"A": []}), ("allows", {"A": True}),
                         ("allows", {"A": ["1","1"]}), ("allows", {"A": ["x"]}), ("allows", {42: ["0"]}),
                         ("allows", {"A": ["0", False]})):
            with self.subTest(key=key), self.assertRaises(ValueError):
                design.plan_design(spec("AB", {**t, key: val}))
        for bad in (True, -1, 1.0, 65536):
            with self.assertRaises(ValueError):
                design.plan_design(s, state_budget=bad)


if __name__ == "__main__":
    unittest.main()
