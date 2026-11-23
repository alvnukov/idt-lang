import unittest
from itertools import product

from scripts import probe_ternary_active_readout as p


class TernaryActiveReadoutTests(unittest.TestCase):
    def test_complete_contact_class_and_active_members(self):
        candidates = p.classify()
        self.assertEqual(len(candidates), 24)
        self.assertEqual(len({entry[2] for entry in candidates}), 24)
        self.assertEqual(sum(m in ("a", "b") for _, m, _ in candidates), 8)
        active = tuple(p.contact(x, y) for x, y in product("abT", repeat=2))
        self.assertIn(("complement-swap", "a", active), candidates)
        for (x, y), (u, v) in zip(product("abT", repeat=2), active, strict=True):
            self.assertEqual(p.contact(v, u), (y, x))
            self.assertEqual(p.contact(u, v), (x, y))
            self.assertEqual((u, v).count("T"), (x, y).count("T"))
            self.assertEqual((u, v).count("b") % 2, (x, y).count("b") % 2)

    def test_native_macro_equals_raw_vacancy_contact_with_recovered_catalyst(self):
        for x, y in product("abT", repeat=2):
            raw = (x, y, "a")
            expected = ((y, x) if "a" in (x, y) else (x, y)) + ("a",)
            self.assertEqual(p.replay(raw, p.VACANCY)[-1], expected)

    def test_ordinary_readout_never_uses_the_held_value_or_postselection(self):
        for x in "abT":
            history = p.replay((x, "b", "b"), p.METER)
            self.assertEqual(history[-1], (x, "a", "a") if x == "T" else (x, "b", "b"))
            self.assertEqual(p.replay(history[-1], p.METER[::-1]), history[::-1])
        self.assertEqual([s.index("T") for s in p.replay(("T", "b", "b"), p.METER)],
                         [0, 0, 1, 2, 0, 1, 2, 0])

    def test_lengths_are_minimal_only_for_the_pinned_triangle_targets(self):
        self.assertEqual(p.triangle_depths(), {"vacancy": 9, "meter": 7})

    def test_complement_neighbor_keeps_marker_stationary_but_cannot_swap_unknown_blanks(self):
        cases = p.audit_local()
        self.assertEqual(cases["complement_stationary_detector_inputs"], 3)
        self.assertEqual(cases["complement_prepared_controlled_swap_rows"], 8)
        self.assertEqual(cases["cs_vacancy_compiler_pairs"], 9)

    def test_protected_meter_shares_catalyst_never_exposing_records_to_T(self):
        for x in "abT":
            history = p.replay((x, "b", "b", "a"), p.PROTECTED_METER)
            self.assertEqual(history[-1], (x, "a", "a", "a") if x == "T" else history[0])
            self.assertTrue(all("T" not in st[1:3] for st in history))
            self.assertEqual(p.replay(history[-1], p.PROTECTED_METER[::-1]), history[::-1])
        self.assertEqual([s.index("T") for s in p.replay(("T", "b", "b", "a"), p.PROTECTED_METER)],
                         [0, 3, 3, 0, 0, 0])
        self.assertEqual(p.protected_depth(), 5)

    def test_all_compiled_launches_are_counted_from_standard_cells(self):
        report = p.verify()
        two = report["two_arm"]
        self.assertEqual((two["launches"], two["ordinary_source_controls"]), (512, 1024))
        self.assertEqual(len(two["rows"]), 32)
        for row in two["rows"]:
            plates, opened = row["plates"], row["opened"]
            dest = row["source"] ^ plates[0] ^ plates[1]
            want = ((16 * (dest == 0), 16 * (dest == 1), 0) if all(opened)
                    else ((4, 4, 8) if any(opened) else (0, 0, 16)))
            self.assertEqual(tuple(row["counts"]), want)
        self.assertEqual(report["three_port"]["hubs"], 192)
        self.assertEqual(report["three_port"]["launches"], 72)
        self.assertEqual(report["resources"]["two_arm_sites"], 25)
        self.assertEqual(report["resources"]["max_two_arm_contacts"], 290)
        self.assertEqual(report["resources"]["three_port_sites"], 16)
        self.assertEqual(report["resources"]["two_arm_graph"], {"edges": 51, "max_degree": 20})
        self.assertEqual(report["resources"]["three_port_graph"], {"edges": 27, "max_degree": 9})


if __name__ == "__main__":
    unittest.main()
