import io
import json
import subprocess
import sys
import unittest
from collections import Counter
from fractions import Fraction as F


class MeasuredIonPentagonTests(unittest.TestCase):
    def test_offline_cli_frozen_counts_and_conditional_result(self):
        run = subprocess.run([sys.executable, "-B", "-O", "-m",
                              "scripts.probe_measured_ion_pentagon", "--json"],
                             capture_output=True, text=True)
        self.assertEqual(run.returncode, 0, run.stderr)
        result = json.loads(run.stdout)
        normal = result["orders"]["normal"]
        self.assertEqual((normal["shots"], normal["unlike"]), (50000, 44690))
        self.assertEqual([normal[k] for k in ("S", "J", "X", "C",
                          "conditional_D_floor", "marginal_TV_sum")],
                         ["4479/2000", "1/200", "4469/2000", "-1969/500", "469/1000", "23/250"])
        self.assertEqual(result["orders"]["reverse"]["unlike"], 44735)
        self.assertIn("not an independent replication", result["boundary"])
        self.assertNotIn("archive_replay", result)

    def test_reverse_vertex_alignment_uses_its_own_order(self):
        from scripts import probe_measured_ion_pentagon as p
        # Each edge records fixed, common labels (1,0,0,0,0) at its two vertices.
        rows = [[0, 0, 10000, 0], [0, 10000, 0, 0]] + [[10000, 0, 0, 0]] * 3
        self.assertEqual(p.score(rows, -1)["marginal_TV_sum"], "0")
        self.assertNotEqual(p.score(rows, 1)["marginal_TV_sum"], "0")

    def test_unequal_edge_denominators_are_not_pooled(self):
        from scripts import probe_measured_ion_pentagon as p
        with self.assertRaisesRegex(p.ProvenanceError, "10000"):
            p.score([[10000, 0, 0, 0]] * 4 + [[9999, 0, 0, 0]], 1)

    def test_one_block_threshold_is_inclusive_and_column_order_is_chronological(self):
        from scripts import probe_measured_ion_pentagon as p
        # 100 trials: (6,7) x 75 and (7,6) x 25.
        raw = ["1.", "10.6", "200"] + ["6", "7"] * 75 + ["7", "6"] * 25
        means = ["1.", "10.6", "-0.5", "0.5", "-1", "0.7575757575757576",
                 "0.7575757575757576", "0"]
        self.assertEqual(p.check_block(raw, means), ((1, F("10.6")), [0, 75, 25, 0]))
        with self.assertRaisesRegex(p.ProvenanceError, "threshold"):
            p.check_block(raw, means[:2] + [means[3], means[2]] + means[4:])
        with self.assertRaisesRegex(p.ProvenanceError, "200"):
            p.check_block(raw[:-1], means)
        with self.assertRaisesRegex(p.ProvenanceError, "key"):
            p.check_block(raw, ["2."] + means[1:])

    def test_full_grid_is_required_before_taking_the_lower_median(self):
        from scripts import probe_measured_ion_pentagon as p
        grid = Counter({(i, F(k, 10)): 100 for i in range(1, 6) for k in range(104, 110)})
        self.assertEqual(p.select_time(grid), F("10.6"))
        grid[2, F("10.8")] -= 1
        with self.assertRaisesRegex(p.ProvenanceError, "grid"):
            p.select_time(grid)

    def test_wrong_archive_is_a_provenance_error_before_zip_parsing(self):
        from scripts import probe_measured_ion_pentagon as p
        fixture = p.load_fixture()
        with self.assertRaisesRegex(p.ProvenanceError, "archive byte length"):
            p.replay_archive(io.BytesIO(b"not an ETH ZIP"), fixture)
        wrong_bytes = bytes(fixture["source"]["archive_bytes"])
        with self.assertRaisesRegex(p.ProvenanceError, "archive SHA-256"):
            p.replay_archive(io.BytesIO(wrong_bytes), fixture)
