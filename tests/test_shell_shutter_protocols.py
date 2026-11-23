import unittest
from collections import Counter
from fractions import Fraction as F

from scripts import probe_shell_shutter_protocols as probe


class ShellShutterProtocolsTest(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.rows = probe.probe_shell_shutters()

    def test_raw_fixture_and_shortest_word_counts(self):
        fixture = probe.cube_fixture()
        self.assertEqual(
            (len(fixture.moves), fixture.centers, fixture.slits), (20, 16, (1, 3, 4))
        )
        # Enumerate enabled raw moves (not a clock-weighted recurrence).
        frontier = [(fixture.start, ())]
        for tick in range(7):
            hits = [word for state, word in frontier if state == fixture.sink]
            if tick < 6:
                self.assertFalse(hits)
                frontier = [
                    (target, word + (center,))
                    for state, word in frontier
                    for center, target in fixture.moves[state].items()
                ]
        self.assertEqual(Counter(word[0] for word in hits), {1: 2, 3: 2, 4: 2})
        for mask, p in enumerate(self.rows["A"][6].sink):
            self.assertEqual(p, F(2 * mask.bit_count(), 16**6))
        self.assertEqual(
            self.rows["B"][6].sink,
            tuple(
                (F(0), F(1, 24), F(5, 144), F(1, 36))[m.bit_count()] for m in range(8)
            ),
        )

    def test_first_nonzero_third_differences(self):
        for name, expected in [
            ("A", (8, F(9, 2147483648))),
            ("B", (6, F(7, 144))),
            ("C", (10, F(9, 549755813888))),
            ("D", None),
        ]:
            with self.subTest(name=name):
                found = next(
                    ((t, r.i3) for t, r in enumerate(self.rows[name]) if r.i3), None
                )
                self.assertEqual(found, expected)
        for row in self.rows["D"]:
            self.assertEqual(row.i2, (0, 0, 0))

    def test_context_symmetry_accounting_and_common_open_law(self):
        for t in range(13):
            for name, timeline in self.rows.items():
                row = timeline[t]
                self.assertTrue(all(type(p) is F for p in row.sink))
                self.assertTrue(
                    all(0 <= p <= q <= 1 for p, q in zip(row.sink, row.retained))
                )
                for k in range(4):
                    self.assertEqual(
                        len({p for m, p in enumerate(row.sink) if m.bit_count() == k}),
                        1,
                    )
                if name in ("A", "B"):
                    self.assertEqual(row.retained, (1,) * 8)
                else:
                    self.assertEqual(row.retained[7], 1)
            for name in ("C", "D"):
                self.assertEqual(self.rows[name][t].sink[7], self.rows["A"][t].sink[7])
        self.assertLess(self.rows["C"][1].retained[0], 1)
        self.assertEqual(self.rows["B"][12].sink[0], 0)  # no enabled center: stay

    def test_killed_kernel_agrees_with_all_touched_decomposition(self):
        fixture = probe.cube_fixture()
        for mask in range(8):
            blocked = {v for j, v in enumerate(fixture.slits) if not mask & (1 << j)}
            counts = Counter({fixture.start: 1})
            for t, row in enumerate(self.rows["C"]):
                self.assertEqual(row.sink[mask], F(counts[fixture.sink], 16**t))
                self.assertEqual(row.retained[mask], F(sum(counts.values()), 16**t))
                following = Counter()
                for state, n in counts.items():
                    for c in range(16):
                        target = fixture.moves[state].get(c, state)
                        if c not in blocked or target == state:
                            following[target] += n
                counts = following

    def test_empty_baseline_is_included(self):
        row = probe.Readout(tuple(F(3 + 2 * m, 20) for m in range(8)), (F(1),) * 8)
        self.assertEqual(row.i2, (0, 0, 0))
        self.assertEqual(row.i3, 0)

    def test_word_feedback_is_not_an_all_touched_path(self):
        fixture = probe.cube_fixture()
        ends = [probe.replay(fixture, mask, probe.FEEDBACK_WORD) for mask in range(8)]
        self.assertEqual(
            [m for m, (state, _) in enumerate(ends) if state == fixture.sink], [4]
        )
        self.assertTrue(all(len(touched) <= 1 for _, touched in ends))

    def test_no_shorter_offer_word_has_a_nonzero_third_difference(self):
        f = probe.cube_fixture()
        # A successful toggle always follows a fully open edge, in every
        # context. Any word that hits in <=7 offers reduces to a fully open
        # successful path after erasing its idle offers. Enumerate all such
        # paths; the only hits have length 6, so at most one idle was erased.
        frontier = [(f.start, ())]
        shortest = []
        for length in range(8):
            for state, word in frontier:
                if state == f.sink:
                    self.assertEqual(length, 6)
                    shortest.append(word)
            if length < 7:
                frontier = [
                    (dest, word + (v,))
                    for state, word in frontier
                    for v, dest in f.moves[state].items()
                ]
        self.assertEqual(len(shortest), 6)
        candidates = set(shortest) | {
            p[:i] + (v,) + p[i:] for p in shortest for i in range(7) for v in range(16)
        }
        for word in candidates:
            val = sum(
                (-1) ** (3 - m.bit_count())
                for m in range(8)
                if probe.replay(f, m, word)[0] == f.sink
            )
            self.assertEqual(val, 0, word)
