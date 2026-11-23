import json
import subprocess
import sys
import unittest
from itertools import product

from scripts import probe_ternary_active_readout as prior


def replay(images, state, word):
    """Replay raw two-port images without importing the selection verifier."""
    table = dict(zip(map("".join, product("abT", repeat=2)), images, strict=True))
    state = list(state)
    history = ["".join(state)]
    for i, j in word:
        state[i], state[j] = table[state[i] + state[j]]
        history.append("".join(state))
    return history


class TernaryOperationalSelectionTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.run_probe = subprocess.run(
            [sys.executable, "-m", "scripts.probe_ternary_operational_selection", "--json"],
            capture_output=True, text=True, check=False,
        )

    def setUp(self):
        self.assertEqual(self.run_probe.returncode, 0, self.run_probe.stderr)
        self.report = json.loads(self.run_probe.stdout)
        self.rows = {row["law"]: row for row in self.report["rows"]}

    def test_exhaustive_independent_census_and_nested_filters(self):
        laws = {f"{blank}/{mixed}": ["".join(p) for p in images]
                for blank, mixed, images in prior.classify()}
        self.assertEqual(self.report["permutations_checked"], 362880)
        self.assertEqual({k: r["images"] for k, r in self.rows.items()}, laws)
        self.assertEqual(self.report["successive_counts"], [24, 8, 4, 2])
        self.assertEqual(set(self.report["survivor_orbit"]),
                         {"complement-swap/a", "complement-swap/b"})
        self.assertEqual(len(self.report["rows"]), 24)

    def test_routing_and_blank_transfer_are_separate_experiments(self):
        for row in self.rows.values():
            im = row["images"]
            route = [replay(im, "T" + c, [(0, 1)])[-1].index("T") for c in "ab"]
            recv = [replay(im, c + "a", [(0, 1)])[-1][1] for c in "ab"]
            self.assertEqual(row["route"] == "witness", route[0] != route[1])
            self.assertEqual(row["transfer"] == "witness", recv[0] != recv[1])
            if row["route"] != "witness":
                for token_first in (False, True):
                    for c in "ab":
                        src = "T" + c if token_first else c + "T"
                        dst = replay(im, src, [(0, 1)])[-1]
                        self.assertEqual(dst.index("T") != src.index("T"),
                                         row["route"] == "always_move")
            if row["transfer"] != "witness":
                for pair in map("".join, product("ab", repeat=2)):
                    dst = replay(im, pair, [(0, 1)])[-1]
                    flip = str.maketrans("ab", "ba")
                    self.assertEqual(dst, pair if row["transfer"] == "self_only"
                                     else pair.translate(flip))

    def test_passive_dye_excludes_any_ordinary_flag_not_only_tested_words(self):
        for dye in "ab":
            row = self.rows["swap/" + dye]
            self.assertEqual(row["record"], "passive_dye")
            for src in map("".join, product("abT", repeat=2)):
                dst = replay(row["images"], src, [(0, 1)])[-1]
                self.assertEqual([c == dye for c in dst], [c == dye for c in src[::-1]])

    def test_constructive_records_restore_all_inputs_and_protect_both_flags(self):
        for name in ("complement-swap/a", "complement-swap/b", "complement/a",
                     "swap/exchange/hold"):
            row = self.rows[name]
            self.assertEqual(row["record"], "witness")
            w = row["record_witness"]
            for x, final in zip("abT", w["finals"], strict=True):
                initial = x + w["stock"]
                trace = replay(row["images"], initial, w["word"])
                self.assertEqual(trace[-1], final)
                self.assertEqual(final[0], x)
                self.assertEqual(final[3:], initial[3:])  # catalyst, when present
                self.assertTrue(all("T" not in step[1:3] for step in trace))
                self.assertEqual(replay(row["images"], final, reversed(w["word"])),
                                 list(reversed(trace)))
                if x != "T":
                    self.assertEqual(final, initial)
                else:
                    self.assertTrue(all(u != v for u, v in zip(initial[1:3], final[1:3])))

    def test_drop_one_counterexamples_really_fail_only_the_omitted_test(self):
        expected = {"route": "swap/exchange/hold", "transfer": "complement/a",
                    "record": "swap/a"}
        self.assertEqual(self.report["drop_one"], expected)
        for omitted, name in expected.items():
            self.assertEqual({k for k in expected if self.rows[name][k] != "witness"},
                             {omitted})
        self.assertEqual(self.rows["swap/exchange/hold"]["record_witness"]["word"],
                         [[0, 1], [0, 2]] * 3)
        self.assertEqual(self.rows["swap/hold"]["record"], "not_evaluated")


if __name__ == "__main__":
    unittest.main()
