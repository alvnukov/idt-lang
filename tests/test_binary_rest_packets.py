"""Exact configuration returns, not marker trajectories or wrapped displacements."""

import unittest

from scripts import probe_binary_rest_packets as probe


class RestPacketTest(unittest.TestCase):
    def test_full_return_and_aliases(self):
        line = probe.GuardedLine(6, 12, 4)
        for word, t, dx, charges in (
            (0, 1, 1, (1, 0)), (1, 4, 2, (0, 0)), (5, 3, 1, (-2, -1)),
        ):
            frames = list(line.replay(word, 3, 0))
            good = [(r.elapsed, r.displacement) for r in frames if r.exact]
            self.assertEqual(good, [(k * t, k * dx) for k in range(1, 12 // t + 1)])
            self.assertEqual(line.charge_difference(word, 3, 0), charges)
        rest = list(line.replay(5, 1, 0))
        self.assertEqual((rest[0].displacement, rest[0].shape, rest[0].medium, rest[0].clock),
                         (0, True, True, False))
        self.assertEqual((rest[1].displacement, rest[1].shape, rest[1].medium, rest[1].clock),
                         (0, True, False, True))

    def test_raw_replay_and_translated_clock_conjugacy(self):
        line = probe.GuardedLine(7, 12, 4)
        for word, f, mask in ((5, 0, 3), (1, 1, 3), (7, 0, 29), (11, 1, 63)):
            frames = list(line.replay(word, mask, f))
            shifted_word = ((word << 1) & 15) | (word >> 3)
            self.assertEqual(frames, list(line.replay(shifted_word, mask << 1, f ^ 1)))
            self.assertEqual(frames, list(line.replay(word, mask, f, raw=True)))

    def test_guard_and_small_ring_alias(self):
        for args in ((0, 4, 2), (2, 0, 4), (3, 6, 3)):
            with self.assertRaises(ValueError):
                probe.GuardedLine(*args)
        line = probe.GuardedLine(3, 8, 2)
        for launch in ((4, 3, 0), (0, 8, 0), (0, 0, 0), (0, 1, 2)):
            with self.assertRaises(ValueError):
                list(line.replay(*launch))
        self.assertGreater(line.origin, 8)
        self.assertGreater(line.cycle.n - line.origin - 3, 8)
        self.assertEqual(probe.winding_control(), {
            "ring_size": 8, "half_steps": 8, "same_ring_state_and_clock": True,
            "lifted_line_displacement": 8,
        })

    def test_edge_cases_by_independent_site_replay(self):
        self.assertEqual(probe.vacuum_edge_checks(), 64)

    def test_against_unbounded_sparse_deviation(self):
        # No ring, padding arithmetic, bit shifts for evolution, or lifted anchor.
        line = probe.GuardedLine(4, 6, 4)
        for word in range(16):
            for mask in (1, 3, 9, 15):
                for phase in (0, 1):
                    base0 = tuple((word >> i) & 1 for i in range(4))
                    seed = {i for i in range(4) if (mask >> i) & 1}
                    base, changed = base0, seed
                    for r in line.replay(word, mask, phase):
                        def update(i, perturb):
                            def read(j):
                                return base[j % 4] ^ (perturb and j in changed)
                            return read(i) ^ (i % 2 == phase and (read(i-1) or read(i+1)))
                        new_base = tuple(update(i, False) for i in range(4))
                        neighbors = {i+d for i in changed for d in (-1, 0, 1)}
                        changed = {i for i in neighbors if update(i, True) != new_base[i % 4]}
                        base = new_base
                        phase ^= 1
                        dx = min(changed) - min(seed)
                        self.assertEqual((r.displacement, r.shape, r.medium, r.clock),
                                         (dx, changed == {i+dx for i in seed},
                                          all(base[i] == base0[(i-dx) % 4] for i in range(4)),
                                          (r.elapsed - dx) % 2 == 0))

    def test_fixed_envelopes(self):
        report = probe.experiment()
        self.assertEqual(report["false_rest_controls"], [
            {"elapsed": 1, "displacement": 0, "shape": True, "medium": True, "clock": False},
            {"elapsed": 2, "displacement": 0, "shape": True, "medium": False, "clock": True},
        ])
        self.assertEqual(report["vacuum"]["launches"], 4096)
        self.assertEqual(report["vacuum"]["first_return_speeds"],
                         {"-1": 8, "1": 8})
        dense = report["periodic"]
        self.assertEqual(dense["launches"], 1024)
        self.assertEqual(dense["no_return_through_horizon"], 894)
        self.assertEqual(dense["first_return_speeds"], {
            "-1": 5, "-1/2": 24, "-1/3": 36, "1/3": 36, "1/2": 24, "1": 5,
        })
        self.assertEqual(dense["neutral_first_return_speeds"], {"-1/2": 24, "1/2": 24})


if __name__ == "__main__":
    unittest.main()
