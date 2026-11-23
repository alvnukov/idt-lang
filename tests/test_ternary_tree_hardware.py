import unittest
from itertools import product

from scripts import probe_ternary_active_readout as cs
from scripts import probe_ternary_tree_hardware as tree


class TreeHardwareTests(unittest.TestCase):
    def test_clean_vacancy_on_tree_and_line(self):
        for x, y in product("abT", repeat=2):
            pair = (y, x) if "a" in (x, y) else (x, y)
            for word, raw, out in (
                (tree.star_word(0, 1, 2, 3), (x, y, "a", "b"), (*pair, "a", "b")),
                (tree.path_word("a"), (x, "a", y, "a"), (pair[0], "a", pair[1], "a")),
                (tree.path_word("b"), (x, "a", y, "b"), (pair[0], "a", pair[1], "b")),
            ):
                self.assertEqual(cs.replay(raw, word)[-1], out)

    def test_protected_meter_exact_history(self):
        for x in "abT":
            rows = cs.replay((x, "b", "b", "a"), tree.meter_word(0, 1, 2, 3))
            flag = "a" if x == "T" else "b"
            self.assertEqual(rows[-1], (x, flag, flag, "a"))
            self.assertFalse(any("T" in row[1:3] for row in rows))
            self.assertEqual(cs.replay(rows[-1], tree.meter_word(0, 1, 2, 3)[::-1]), rows[::-1])

    def test_blank_conjugation_and_charge(self):
        for x, y in product("abT", repeat=2):
            u, v = cs.contact(x, y)
            self.assertEqual(tree.charge((u, v), (1, -1)), tree.charge((x, y), (1, -1)))
            if "T" not in (x, y):
                self.assertEqual((u, cs.FLIP[v]), (cs.FLIP[y], x))
        self.assertNotEqual(tree.charge("ab", (1, -1)), tree.charge("ba", (1, -1)))

    def test_bounded_path_search(self):
        rows = tree.path_search()
        self.assertEqual({k: row["shortest_within_24"] for k, row in rows.items()},
                         {"aa": 19, "ab": 19, "ba": None, "bb": None})

    def test_assembled_fixtures_and_physical_resources(self):
        report = tree.verify()
        for name, expected in (("two_arm", (26, 25, 17, 25, 490)),
                               ("three_port", (17, 16, 10, 13, 300))):
            res = report[name]["resources"]
            self.assertEqual(tuple(res[k] for k in ("sites", "edges", "max_degree",
                                                    "offered_edges", "max_contacts")), expected)
        self.assertEqual(len(report["two_arm"]["rows"]), 32)
        self.assertEqual(report["two_arm"]["launches"], 512)
        self.assertEqual(report["two_arm"]["ordinary_source_controls"], 1024)
        self.assertEqual(report["three_port"]["hubs"], 192)
        self.assertEqual(report["three_port"]["launches"], 72)


if __name__ == "__main__":
    unittest.main()
