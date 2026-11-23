import unittest
from itertools import product

from scripts import probe_ternary_vacancy_switch as p
from scripts import probe_vacuum_compensated_network as frozen


class TernaryVacancySwitchTests(unittest.TestCase):
    def test_contact_factor_and_scratch_swap_on_entire_alphabet(self):
        for a, b in product("VNT", repeat=2):
            out = p.contact(a, b)
            self.assertEqual(out, (b, a) if "V" in (a, b) else (a, b))
            self.assertEqual(p.occupancy(out), p.occupancy((b, a)))
            self.assertEqual(p.replay((a, b, "V"), p.triangle(0, 1, 2))[-1], (b, a, "V"))

    def test_filled_controls_freeze_and_path_contacts_cannot_overtake(self):
        for a, b in product("NT", repeat=2):
            raw = (a, b, "N")
            self.assertEqual(p.replay(raw, p.triangle(0, 1, 2)), (raw,) * 4)
        for raw in product("VNT", repeat=5):
            for i in range(4):
                end = p.replay(raw, ((i, i + 1),))[-1]
                self.assertEqual(
                    tuple(x for x in raw if x != "V"), tuple(x for x in end if x != "V")
                )

    def test_two_arm_rows_records_and_source_indistinguishability(self):
        for source, plates, opened in product(range(2), p.BITS, p.BITS):
            counts = [0] * 3
            for seeds, fills in product(p.BITS, repeat=2):
                tr = p.trial(source, plates, opened, seeds, fills)
                other = p.trial(1 - source, plates, opened, seeds, fills)
                self.assertEqual(
                    tuple(map(p.occupancy, tr.states)), tuple(map(p.occupancy, other.states))
                )
                self.assertEqual(p.replay(tr.states[-1], tr.word[::-1]), tr.states[::-1])
                for arm in range(2):
                    old = (
                        "T" if arm == source ^ seeds[0] ^ seeds[1] else "N",
                        *p.stock(seeds[arm] ^ plates[arm]),
                    )
                    self.assertEqual(
                        tr.record(arm), ("V", *p.stock(fills[arm])) if opened[arm] else old
                    )
                for j, v in enumerate(tr.outcome):
                    counts[j] += v
            dest = source ^ plates[0] ^ plates[1]
            want = (
                [16 * (dest == 0), 16 * (dest == 1), 0]
                if all(opened)
                else ([4, 4, 8] if any(opened) else [0, 0, 16])
            )
            self.assertEqual(counts, want)

    def test_three_port_words_match_frozen_comparator_at_each_checkpoint(self):
        for edges, source, bits in product(
            (frozen.CHAIN, frozen.TRIANGLE, frozen.REPEATED), range(3), product(range(2), repeat=3)
        ):
            old = [(3 if i == source else 1, 1 + bit) for i, bit in enumerate(bits)]
            for step, (a, b) in zip(p.network(source, bits, edges), edges, strict=True):
                old[a], old[b] = frozen.device((old[a], old[b]), "U")
                self.assertEqual(
                    step, tuple(("T" if d == 3 else "N", *p.stock(e - 1)) for d, e in old)
                )

    def test_report_distinguishes_operating_code_from_ordinary_occupancy(self):
        report = p.verify()
        self.assertEqual(report["two_arm"]["launches"], 512)
        self.assertEqual(report["two_arm"]["pinned_dump_interventions"], 256)
        self.assertEqual(report["network"]["launches"], 72)
        self.assertEqual(report["network"]["compared_hubs"], 192)
        self.assertEqual(report["resources"]["max_two_arm_degree"], 5)
        self.assertEqual(report["resources"]["max_two_arm_contacts"], 30)
        self.assertIn("occupancy", report["scope"])


if __name__ == "__main__":
    unittest.main()
