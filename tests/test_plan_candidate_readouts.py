"""Exercise the public advisory interface; a completed plan never mutates history."""

import json
import subprocess
import sys
import unittest
from pathlib import Path

from scripts.plan_candidate_readouts import _object, follow
from scripts.probe_active_readout_panels import (
    SCHEMA,
    network_design,
    probe,
    stream_design,
)
from theory_experiments.discrimination_design import plan_design

ROOT = Path(__file__).resolve().parents[1]


class PlanCandidateReadoutTests(unittest.TestCase):
    def test_predictor_generated_menus_keep_unmodeled_and_real_aliases(self):
        result = probe()["menus"]
        self.assertEqual((result["stream"]["worst_cost"],result["network"]["worst_cost"]),(8,15))
        self.assertEqual((result["stream"]["optimal_fixed_cost"],result["network"]["optimal_fixed_cost"]),(8,19))
        self.assertEqual((len(stream_design()["tests"]),len(network_design()["tests"])),(5,18))
        for menu in result.values():
            self.assertTrue(all("unmodeled" in end for end in menu["retained_terminal_sets"]))
        self.assertIn(["F101","mobile"],result["network"]["unseparable_pairs"])
        self.assertIn(["stock","wire"],result["network"]["unseparable_pairs"])
        self.assertNotIn(["bucket","rotor"],result["stream"]["unseparable_pairs"])

    def test_outside_library_is_reported_but_trailing_and_bad_labels_fail(self):
        spec = {"schema":SCHEMA,"models":["a","b"],"tests":[{"id":"t","cost":1,"outcomes":["x","y","z"],
                 "allows":{"a":["x"],"b":["y"]}}]}
        p=plan_design(spec)
        self.assertEqual(follow(p,[])["outside_library_labels"],["z"])
        self.assertEqual(follow(p,["z"]),{"status":"outside_submitted_library","next_test":None,"survivors":[]})
        self.assertEqual(follow(p,["x"])["survivors"],["a"])
        for word in (["z","x"],["x","z"],["unknown"]):
            with self.assertRaises(ValueError):
                follow(p,word)
        empty=plan_design(spec,state_budget=0)
        self.assertEqual(follow(empty,[])["survivors"],["a","b"])
        with self.assertRaises(ValueError):
            follow(empty,["x"])
        with self.assertRaises(ValueError):
            json.loads('{"left":null,"left":["x"]}',object_pairs_hook=_object)

    def test_cli_sorted_result_and_bounded_full_dag(self):
        cmd=[sys.executable, "-B",str(ROOT/"scripts"/"plan_candidate_readouts.py"),"--demo","stream"]
        out=subprocess.run(cmd+["--full","--outcome","yes"],check=True,capture_output=True,text=True)
        doc=json.loads(out.stdout)
        self.assertEqual(doc["current"]["next_test"],"first_net_is_one")
        self.assertEqual(doc["current"]["survivors"],["bucket","rotor","unmodeled"])
        self.assertLess(len(doc["plan"]["nodes"]),10)
        small=subprocess.run(cmd+["--state-budget","0"],check=False,capture_output=True,text=True)
        self.assertEqual(small.returncode,2)
        self.assertEqual(json.loads(small.stdout)["current"]["status"],"budget_exhausted")
