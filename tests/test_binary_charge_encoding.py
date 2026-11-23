import json
import subprocess
import sys
import unittest

from scripts import probe_binary_unanimous_triples as binary
from scripts import probe_blind_collision_charge as native


class BinaryChargeEncoding(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        run = subprocess.run([sys.executable, "-m", "scripts.probe_binary_charge_encoding"],
                             capture_output=True, text=True)
        if run.returncode:
            raise AssertionError(run.stderr)
        cls.report = json.loads(run.stdout)

    def test_all_sitewise_polarities_and_channel_placements(self):
        r = self.report["direct"]
        self.assertEqual(r["addressed_polarities"], 2**15)
        self.assertEqual(r["preserving"], {"A": 64, "B": 32, "C": 54, "AB": 4,
                                          "AC": 6, "BC": 0, "ABC": 0})
        self.assertEqual(r["common_polarities_passing_each_forward_C_edge"], [0]*6)

    def test_dual_rail_words_on_all_raw_logical_inputs(self):
        r = self.report["dual_rail"]
        self.assertEqual(len(r), 21)
        for row in r:
            k = {"A": 1, "B": 2, "C": 3}[row["channel"][0]]
            self.assertEqual(row["verified_inputs"], 32**k)
            self.assertEqual(row["prepared_zero_sites"], 5*k - 2)
            self.assertEqual(row["prepared_high_sites"], 1)
        c, = [row for row in r if row["channel"] == "C"]
        self.assertEqual((c["endpoint_pairs"], c["E_offers"], c["sites"]), (18, 2646, 44))

    def test_scalar_raw_contacts_with_named_packet_order_and_wrong_helper(self):
        from scripts import probe_binary_charge_encoding as p
        c, = [channel for channel in p.menu() if channel.name == "C"]
        word = tuple(p.contact_word(c))
        high = 43
        encode = lambda cfg: sum(1 << (2*(5*i + j) + ((x >> j) & 1))
                                 for i, x in enumerate(cfg) for j in range(5))
        start = encode((0, 0, 9)) | (1 << high)
        end = encode((30, 30, 23)) | (1 << high)
        history = binary.trace(start, word)
        self.assertEqual(history[-1], end)
        self.assertEqual(binary.trace(end, word[::-1])[-1], start)
        self.assertTrue(all(x.bit_count() % 3 == start.bit_count() % 3 for x in history))
        self.assertTrue(any(((x >> (2*j)) & 3) not in (1, 2)
                            for x in history[1:-1] for j in range(15)))
        self.assertNotEqual(binary.trace(start ^ (1 << high), word)[-1], end ^ (1 << high))
        _, rules = native.ternary_library()
        self.assertEqual(native.fire((0, 0, 9), rules[(1, 1, "large", 1)]), (30, 30, 23))

    def test_actual_legal_trajectories_forbid_static_additive_q_lift_for_this_word(self):
        from scripts import probe_binary_charge_encoding as p
        c, = [row for row in self.report["dual_rail"] if row["channel"] == "C"]
        ctrl = c["per_step_real_additive_control"]
        self.assertEqual(ctrl["forced_zero_rail_slopes"], list(range(15)))
        self.assertEqual(ctrl["required_q_slopes"], [-2, -2, -2, 3, 3]*3)
        op, = [op for op in p.menu() if op.name == "C"]
        word = tuple(p.contact_word(op))
        changed_contacts = []
        for step, logical_input in ctrl["example_step_and_input"]:
            self.assertTrue(all(((logical_input >> (5*i)) & 31) in native.STATES for i in range(3)))
            raw = (1 << 43) | sum(1 << (2*j + ((logical_input >> j) & 1)) for j in range(15))
            walk = binary.trace(raw, word[:step])
            self.assertNotEqual(walk[-2], walk[-1])
            changed_contacts.append(set(word[step-1]))
        self.assertEqual(changed_contacts[0] ^ changed_contacts[1], {0, 1})
