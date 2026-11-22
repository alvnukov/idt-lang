"""Exact population compatibility checks, not sampled-data inference."""

import copy
from fractions import Fraction as F
import io
import json
from pathlib import Path
import tempfile
import unittest
from contextlib import redirect_stdout, redirect_stderr

from scripts.check_contact_tomogram import SCHEMA, check_tomogram, main, psd_rank
from scripts.probe_connected_contact_tomography import branch_fraction, connected, known_moment, path_between


def table(ensemble, n, edges):
    graph = connected(n, edges)
    names = [f"r{i}" for i in range(n)]
    return {"schema": SCHEMA, "rails": names, "edges": [[names[i], names[j]] for i,j in edges],
            "measurements": [{"pair": [names[i], names[j]],
                              "h": str(branch_fraction(ensemble, path_between(graph, i, j)))}
                             for i in range(n) for j in range(i+1, n)]}


class ContactTomogramTests(unittest.TestCase):
    def test_pure_and_mixed_all_sizes_and_shortest_path_ties(self):
        for n in range(2, 9):
            edges = [(i, i+1) for i in range(n-1)]
            a = (1, -1)+(0,)*(n-2)
            b = (0,)*(n-2)+(1, -1)
            for ensemble in (((1,a),), ((1,a),(2,b))):
                result = check_tomogram(table(ensemble,n,edges))
                self.assertTrue(result["compatible"])
                self.assertTrue(result["all_input_consistent"])
                self.assertEqual(result["moment"], [[str(x) for x in r] for r in known_moment(ensemble)])
                self.assertEqual(result["rank"], 1 if n == 2 or len(ensemble) == 1 else 2)
        diamond = [(0,1),(0,2),(1,3),(2,3)]
        value = table(((1,(1,0,-1,0)),),4,diamond)
        result = check_tomogram(value)
        self.assertIn({"pair":["r0","r3"],"path":["r0","r1","r3"]}, result["programs"])
        value["edges"].reverse()
        self.assertEqual(check_tomogram(value), result)

    def test_psd_zero_and_negative_pivots(self):
        self.assertEqual(psd_rank([[0,0],[0,1]]), (True,1))
        self.assertEqual(psd_rank([[0,1],[1,0]]), (False,None))
        self.assertEqual(psd_rank([[1,2],[2,1]]), (False,None))
        self.assertEqual(psd_rank([[-1,0],[0,2]]), (False,None))
        self.assertEqual(psd_rank([[1,1],[1,1]]), (True,1))

    def test_bounded_but_nonphysical_and_trace_failure(self):
        value = table(((1,(1,-1,0)),),3,[(0,1),(1,2)])
        for h in value["measurements"]:
            h["h"] = "0"
        result = check_tomogram(value)
        self.assertFalse(result["compatible"])
        self.assertEqual(result["trace"], "0")
        value["edges"] = [["r0","r1"],["r0","r2"],["r1","r2"]]
        # D=(0,1,2) has trace one and violates zero-distance identification.
        for row,h in zip(value["measurements"],("0","1/2","1")):
            row["h"] = h
        result = check_tomogram(value)
        self.assertEqual(result["trace"], "1")
        self.assertFalse(result["positive_semidefinite"])
        self.assertEqual(result["rank"], 2)
        self.assertFalse(result["compatible"])

    def test_malformed_tables(self):
        base = table(((1,(1,-1,0)),),3,[(0,1),(1,2)])
        variants = []
        for bad in (True, 0.5, "1/0", "NaN", {}, -1, "2"):
            v=copy.deepcopy(base); v["measurements"][0]["h"]=bad; variants.append(v)
        v=copy.deepcopy(base); v["measurements"].pop(); variants.append(v)
        v=copy.deepcopy(base); v["measurements"].append(v["measurements"][0]); variants.append(v)
        v=copy.deepcopy(base); v["measurements"][0]["pair"].reverse(); variants.append(v)
        v=copy.deepcopy(base); v["edges"]=[["r0","r1"]]; variants.append(v)
        v=copy.deepcopy(base); v["rails"][1]="r0"; variants.append(v)
        v=copy.deepcopy(base); v["edges"].append(v["edges"][0]); variants.append(v)
        v=copy.deepcopy(base); v["extra"]=0; variants.append(v)
        for v in variants:
            with self.subTest(value=v), self.assertRaises(ValueError):
                check_tomogram(v)

    def test_drift_can_pass_one_path_compatibility(self):
        # Each program is emitted by a different preparation, yet the table
        # equals a single pure target. Compatibility cannot certify no drift.
        target=(1,0,-1)
        v=table(((1,target),),3,[(0,1),(1,2)])
        # Program (0,1) is insensitive to swapping the two endpoint amplitudes.
        alternate=(0,1,-1)
        self.assertNotEqual(known_moment(((1,target),)), known_moment(((1,alternate),)))
        self.assertEqual(branch_fraction(((1,target),),(0,1)),
                         branch_fraction(((1,alternate),),(0,1)))
        v["measurements"][0]["h"]=str(branch_fraction(((1,alternate),),(0,1)))
        self.assertTrue(check_tomogram(v)["compatible"])
        self.assertIn("one_path_compatible_only",check_tomogram(v)["scope"])

    def test_cli_exit_distinction_and_duplicate_json_keys(self):
        with tempfile.TemporaryDirectory() as directory:
            path=Path(directory)/"table.json"
            value=table(((1,(1,-1)),),2,[(0,1)])
            with redirect_stdout(io.StringIO()), redirect_stderr(io.StringIO()):
                path.write_text(json.dumps(value)); self.assertEqual(main([str(path)]),0)
                value["measurements"][0]["h"]="0"
                path.write_text(json.dumps(value)); self.assertEqual(main([str(path)]),1)
                path.write_text('{"schema":0,"schema":1}'); self.assertEqual(main([str(path)]),2)


if __name__ == "__main__":
    unittest.main()
