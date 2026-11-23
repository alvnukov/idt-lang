import unittest
from fractions import Fraction as Q

from scripts import probe_pair_response_span as probe


def dot(a, b):
    return sum(x * y for x, y in zip(a, b, strict=True))


class PairResponseSpanTests(unittest.TestCase):
    def verify_witness(self, rows, y, result):
        self.assertEqual(result["status"], "not_sufficient")
        left, right, null = (result[k] for k in ("left", "right", "null"))
        for weights in (left, right):
            self.assertTrue(all(w >= 0 for w in weights))
            self.assertEqual(sum(weights), 1)
        for row in [(1,) * len(y), *rows.values()]:
            self.assertEqual(dot(row, null), 0)
            self.assertEqual(dot(row, left), dot(row, right))
        self.assertNotEqual(dot(y, null), 0)
        self.assertNotEqual(dot(y, left), dot(y, right))

    def test_affine_not_merely_linear_decoder(self):
        rows = {"x": [0, Q(1, 2), 1], "twice_x": [0, 1, 2]}
        y = [2, 5, 8]
        answer = probe.response_span(rows, y)
        self.assertEqual(answer["status"], "sufficient")
        self.assertEqual(answer["rank"], 2)
        for i, target in enumerate(y):
            self.assertEqual(sum(c * (1 if name == "normalization" else rows[name][i])
                                 for name, c in answer["decoder"].items()), target)

    def test_all_pure_vectors_distinct_but_mixtures_collide(self):
        rows = {"x": [0, Q(1, 2), 1]}
        y = [0, 1, 0]
        ans = probe.response_span(rows, y)
        self.verify_witness(rows, y, ans)
        self.assertEqual({tuple(ans["left"]), tuple(ans["right"])},
                         {(Q(1, 2), 0, Q(1, 2)), (0, 1, 0)})

    def test_fail_closed(self):
        for rows, y in (({}, []), ({"x": [0]}, [0, 1]), ({"x": [None]}, [0]),
                        ({"normalization": [0]}, [0]), ({}, [0.5])):
            with self.subTest(rows=rows, y=y), self.assertRaises(ValueError):
                probe.response_span(rows, y)

    def test_c16_native_mixtures_and_decoder(self):
        rows, future = probe.c16_table()
        self.assertEqual(len(rows), 32 + 496)
        pair = future["next:S0,S3"]
        self.assertTrue(all(row[0] == row[1] for row in rows.values()))
        self.assertEqual(pair[:2], [0, Q(1, 32)])
        result = probe.response_span(rows, pair)
        self.assertEqual(result["rank"], 4)
        self.verify_witness(rows, pair, result)
        self.assertEqual(future["next:short_count"], [2] * len(pair))
        self.assertEqual(probe.response_span(rows, future["next:short_count"])["decoder"],
                         {"normalization": 2})
        idle_rows = {k: v[2:] for k, v in rows.items()}
        self.assertEqual(len(set(zip(*idle_rows.values()))), 4)
        triple = future["current:S0,L3,L4"][2:]
        ans = probe.response_span(idle_rows, triple)
        self.verify_witness(idle_rows, triple, ans)
        self.assertEqual({dot(triple, ans[k]) for k in ("left", "right")}, {0, Q(1, 64)})


if __name__ == "__main__":
    unittest.main()
