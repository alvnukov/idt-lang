"""Independent constant-memory full enumeration versus compressed Python classifications."""

import itertools
import json
import shutil
import subprocess
import tempfile
import unittest
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]


def expand(words):
    out = set()
    for word in words:
        choices = [range(8) if v == "*" else (int(v),) for v in word]
        for row in itertools.product(*choices):
            packed = sum(v << (3*i) for i,v in enumerate(row))
            if packed in out:
                raise AssertionError("overlapping survivor cubes")
            out.add(packed)
    return out


class ExhaustiveCellOracleTests(unittest.TestCase):
    @unittest.skipUnless(shutil.which("cc"),"independent C compiler not installed")
    def test_all_sixteen_million_tables_and_exact_winner_ids(self):
        oracle = ROOT / "scripts" / "audit_cell_census.c"
        with tempfile.TemporaryDirectory() as tmp:
            exe = Path(tmp)/"audit_cell"
            subprocess.run(["cc","-std=c11","-O2","-Wall","-Wextra","-Werror",str(oracle),"-o",str(exe)],
                           check=True,capture_output=True,timeout=60)
            run = subprocess.run([str(exe),"--survivors"],check=True,text=True,
                                 capture_output=True,timeout=60)
        winners = {"time":set(),"full":set()}
        counts = {}
        for line in run.stdout.splitlines():
            label,*values = line.split()
            vals = list(map(int,values))
            if label == "id":
                idx,full = vals
                self.assertIn(full,(0,1))
                self.assertNotIn(idx,winners["time"])
                winners["time"].add(idx)
                if full:
                    winners["full"].add(idx)
            else:
                self.assertIn(label,winners)
                self.assertNotIn(label,counts)
                counts[label] = vals
        saved = json.loads((ROOT / "data" / "unrestricted_cell_census.json").read_text())
        for name,winner_ids in winners.items():
            mode = saved["modes"][name]
            self.assertEqual(sum(counts[name]),8**8)
            self.assertEqual(counts[name][-1],len(winner_ids))
            self.assertEqual(counts[name][:-1],mode["first_failure_counts"])
            self.assertSetEqual(winner_ids,expand(mode["winning_cubes"]))
