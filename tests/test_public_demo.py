"""Public output contracts, independent numerical witnesses, and fail-closed cases."""

import contextlib
import io
import json
import subprocess
import sys
import unittest
from fractions import Fraction as F
from pathlib import Path
from unittest.mock import patch

from scripts import public_demo as demo


class PublicDemoTests(unittest.TestCase):
    def test_port_against_rational_reflections(self):
        row = demo.same_port_fixture()
        value = list(map(F, (1, 0, 0, 0)))
        self.assertEqual(row["contacts"], [[0, 1, 2], [1, 2, 3]] * 2)
        for h in row["contacts"]:
            twice_mean = F(2, 3) * sum(value[i] for i in h)
            for i in h:
                value[i] = twice_mean - value[i]
        selected = value[row["port"]]
        self.assertEqual((row["after"], row["port"], row["submitted_dark"]), (4, 3, True))
        self.assertNotEqual(selected, 0)
        self.assertEqual((selected.numerator % 5, selected.denominator % 5 == 0), (0, False))
        a, b = (row["candidates"][n] for n in ("modfive_dark_mobile", "modfive_dark_prime"))
        self.assertEqual((a["predicted_dark"], b["predicted_dark"]), (False, True))
        self.assertEqual((a["status"], b["status"]), ("counterexample", "no_counterexample_within_bounds"))

    def test_json_from_outside_repository(self):
        cmd = [sys.executable, "-B", str(demo.ROOT / "scripts/public_demo.py"), "--json"]
        proc = subprocess.run(cmd, cwd=Path(sys.executable).parent, check=True,
                              capture_output=True, text=True, timeout=25)
        out = json.loads(proc.stdout)
        self.assertEqual(out["schema"], "idt-public-demo/1")
        self.assertEqual(set(out), {"schema", "detector", "same_port", "shutter", "planning",
                                    "governance", "boundary"})
        d, s, p, g = (out[k] for k in ("detector", "shutter", "planning", "governance"))
        self.assertEqual((d["minus_four_counts"], d["plus_four_counts"]), (64584, 64452))
        self.assertEqual((p["adaptive_worst_cost"], p["best_fixed_cost"]), (15, 19))
        self.assertTrue(p["wildcard_retained_at_all_leaves"])
        for label in ("before", "after"):
            stock = [F(k, 1+k) for k in s[f"leaves_{label}"]]
            self.assertEqual(F(s[f"first_arm_share_{label}"]), stock[0] / sum(stock))
        self.assertEqual(g["issues"], 0)
        self.assertTrue(g["verifier_ok"])
        self.assertGreater(g["checks"], 0)
        manifest = json.loads((demo.ROOT / demo.MANIFEST_FILE).read_bytes())
        self.assertEqual(g["symbol_status"], {k: manifest["symbols"][k]["status"] for k in demo.TARGETS})
        self.assertEqual(g["blocked_derivation_ids_for_selected_targets"],
                         [d["id"] for d in manifest["derivations"]
                          if d["target"] in demo.TARGETS and d["status"] == "blocked"])
        human = demo.human(out)
        for label in ("Measured:", "Finite target:", "Test design:", "Shutter model:", "Governance:"):
            self.assertIn(label, human)

    def test_failures_are_nonzero_without_partial_success(self):
        for name, error in (("detector_histogram", ValueError("bad histogram")),
                            ("governance", subprocess.TimeoutExpired("verifier", 15))):
            with self.subTest(section=name), patch.object(demo, name, side_effect=error):
                stdout, stderr = io.StringIO(), io.StringIO()
                with contextlib.redirect_stdout(stdout), contextlib.redirect_stderr(stderr):
                    self.assertNotEqual(demo.main(["--json"]), 0)
                self.assertFalse(stdout.getvalue())
                self.assertIn("public_demo:", stderr.getvalue())
        with (patch("scripts.public_demo.subprocess.run",
                    return_value=subprocess.CompletedProcess([], 1, stdout="{}", stderr="failed")),
              self.assertRaisesRegex(ValueError, "could not certify")):
            demo.governance()


if __name__ == "__main__":
    unittest.main()
