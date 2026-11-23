"""Exact finite census and independent raw-contact/graph controls."""

import unittest
from collections import Counter, deque
from typing import ClassVar

from scripts import probe_octagon_three_contexts as probe


def raw_endpoint(maps: probe.Maps, word: str, start: int) -> int:
    """Apply four literal bit complements; do not step a permutation."""
    bits = [int(i // 2 == start) for i in range(2 * len(maps["A"]))]
    for letter in word:
        contacts = []
        for i, j in enumerate(maps[letter]):
            if i < j:
                pins = (2*i, 2*i+1, 2*j, 2*j+1)
                if sum(bits[k] for k in pins) == 2:
                    contacts.append(pins)
        if len(contacts) != 1:
            raise ValueError(f"expected one legal contact, got {contacts}")
        for k in contacts[0]:
            bits[k] = 1 - bits[k]
    occupied = [i for i in range(len(bits)) if bits[i]]
    if len(occupied) != 2 or occupied[0] % 2 or occupied[1] != occupied[0] + 1:
        raise ValueError("raw packet left the prepared sector")
    return occupied[0] // 2


def brute_girth(maps: probe.Maps) -> int:
    """Remove an edge, then find the shortest alternate path between its ends."""
    size = len(maps["A"])
    best = size + 1
    for mapping in maps.values():
        for u, v in enumerate(mapping):
            if u >= v:
                continue
            seen, queue = {u}, deque([(u, 0)])
            while queue:
                x, length = queue.popleft()
                if x == v:
                    best = min(best, length + 1)
                    break
                for color in maps.values():
                    y = color[x]
                    if not (x == u and y == v) and y not in seen:
                        seen.add(y)
                        queue.append((y, length + 1))
    return best


class ThreeContextTests(unittest.TestCase):
    report: ClassVar[probe.ProbeReport]

    @classmethod
    def setUpClass(cls) -> None:
        cls.report = probe.run_probe()

    def test_eight_site_controls(self) -> None:
        one = self.report["single_octagon"]
        self.assertEqual(sum(one["joint_counts"].values()), 105)
        self.assertEqual(one["joint_counts"],
                         {"I,I": 5, "I,Z": 4, "I,other": 16,
                          "Z,I": 4, "Z,Z": 0, "Z,other": 0,
                          "other,I": 16, "other,Z": 0, "other,other": 60})
        self.assertEqual(one["both_identity_and_W_squared_Z"], 5)
        self.assertEqual(one["simple_cubic_girth_at_least_six"], 0)

    def test_minimal_census_and_single_colored_class(self) -> None:
        two = self.report["two_octagons"]
        self.assertEqual(two["girth_counts"], {4: 37488, 5: 2816, 6: 16})
        self.assertEqual(two["all_bicolored_octagons"], 552)
        self.assertEqual(two["tested"], 40320)
        self.assertEqual(two["accepted"], 8)
        self.assertEqual(two["minimum_connected_component_size"], 16)
        self.assertEqual(two["accepted_affine_parameters"],
                         [[s, d] for s in (3, 5) for d in range(8)
                          if s * (-1)**d % 8 == 5])
        self.assertEqual(two["colored_isomorphism_classes"], 1)

    def test_girth_and_second_returns_with_labels_fixed(self) -> None:
        for s, d, girth, period in ((5, 0, 6, 8), (3, 0, 6, 16),
                                    (1, 0, 4, 4), (3, 1, 6, 8)):
            f = tuple((s*i + d) % 8 for i in range(8))
            maps = probe.two_rings(f)
            self.assertEqual(probe.ring_girth(f), brute_girth(maps))
            self.assertEqual(brute_girth(maps), girth)
            for pair in ("AC", "BC"):
                lengths = probe.bicolored_lengths(maps, pair)
                self.assertEqual(lengths, [period] * (16 // period))
        f = (0, 2, 4, 1, 5, 7, 3, 6)
        self.assertEqual(brute_girth(probe.two_rings(f)), 5)
        self.assertEqual(probe.ring_girth(f), 5)

    def test_raw_positive_endpoint_actions_and_signed_differences(self) -> None:
        for maps in (probe.two_rings(tuple(5*i % 8 for i in range(8))),
                     probe.lifted_control()):
            for word in ("ABAB", "ACAC", "BCBC", "ABCABC", "ABABC", "CABAB"):
                self.assertEqual(probe.action(maps, word), tuple(
                    raw_endpoint(maps, word, i) for i in range(len(maps["A"]))))
        base = probe.two_rings(tuple(5*i % 8 for i in range(8)))
        z, w = probe.action(base, "ABAB"), probe.action(base, "ABC")
        for i, j in enumerate(z):
            self.assertNotEqual(i, j)
            if i < j:
                signed = Counter({w[w[i]]: 1, w[w[j]]: -1})
                self.assertEqual(signed, Counter({i: -1, j: 1}))
        self.assertEqual(self.report["minimal_action"]["opposite_difference_dimension"], 8)

    def test_connected_larger_countermodel(self) -> None:
        row = self.report["double_cover"]
        maps = probe.lifted_control()
        self.assertEqual(brute_girth(maps), 6)
        self.assertEqual(row["component_size"], 32)
        self.assertEqual(row["bicolored_lengths"],
                         {p: [8]*4 for p in ("AB", "AC", "BC")})
        self.assertEqual(row["from_zero"],
                         {"ABAB": 20, "ACAC": 20, "BCBC": 4,
                          "ABABC": 28, "CABAB": 12})
        with self.assertRaises(ValueError):
            probe.check_minimal_action(maps)
