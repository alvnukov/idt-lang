"""Binary-only shared-cut dimension certificates; never a physical status upgrade."""

import copy
import hashlib
import json
import unittest
from dataclasses import asdict, replace
from fractions import Fraction as F
from itertools import combinations, permutations, product
from pathlib import Path
from unittest.mock import patch

from theory_experiments import binary_overlap_cut as adapter
from theory_experiments.primitive_screen import Limits


def spec(table, *, dim=2, model="quantum", basis="unconditional", seed=True):
    def cell(p):
        a, b = p if isinstance(p, tuple) else (p, p)
        return [str(a), str(b)]
    return {"id": "test_cut", "family": "binary_overlap_cut", "event": "ref",
            "event_basis": basis, "memory": {"model": model, "dimension": dim,
                                             "shared_classical_seed": seed},
            "intervals": [[cell(p) for p in row] for row in table]}


def box(table, radius):
    return [[(max(0, p-radius), min(1, p+radius)) for p in row] for row in table]


def evaluate(raw, *, max_cases=1000, deadline=None):
    (check,), details = adapter.evaluate_binary_overlap_cut(
        adapter.parse_binary_overlap_cut(raw), Limits(max_cases=max_cases), deadline=deadline)
    return check, details


class BinaryOverlapTests(unittest.TestCase):
    def test_raw_noisy_5x5_certificate_independent_integer_replay(self):
        d = 5
        table = [[F(1, 1+36*(i-j)**2) for j in range(d)] for i in range(d)]
        raw = spec(box(table, F(39,4000)), dim=4)
        c, info = evaluate(raw)
        self.assertEqual((c.status, c.checked, c.planned), ("counterexample", 10, 10))
        w = c.witness["inputs"]
        grid = w["tick_denominator"]
        pair_rows = w["pair_certificate"]
        self.assertEqual(len(pair_rows), 10)
        intervals = adapter.parse_binary_overlap_cut(raw).intervals

        def is_upper(k, left, right):
            if not (left[1] < right[0] or right[1] < left[0]):
                return k >= grid
            p,q = (left[1],right[0]) if left[1] < right[0] else (right[1],left[0])
            a,b = p*q,(1-p)*(1-q)
            excess = F(k,grid)-a-b
            return excess >= 0 and excess**2 >= 4*a*b

        for (i,j), (y,k) in zip(combinations(range(d),2),pair_rows):
            # An independent radical-free check: k is the smallest safe tick
            # across all settings and y is the first setting safe at that tick.
            self.assertTrue(is_upper(k,intervals[i][y],intervals[j][y]))
            self.assertFalse(any(is_upper(k-1,a,b) for a,b in zip(intervals[i],intervals[j])))
            self.assertFalse(any(is_upper(k,intervals[i][t],intervals[j][t]) for t in range(y)))
        total = d+2*F(sum(k for _,k in pair_rows),grid)
        self.assertEqual(F(w["ordered_overlap_sum_upper"]),total)
        self.assertEqual(F(c.witness["actual"]),4*total-d*d)
        self.assertLess(4*total,d*d)
        self.assertEqual(info["rejection_scope"],adapter.SCOPE)
        self.assertEqual((info["scientific_status"], info["empirical_status"], info["proof_status"]),
                         ("unassessed", "not_tested", "not_attempted"))
        self.assertIn("simultaneous",info["interval_coverage_status"])
        self.assertEqual(evaluate(raw),(c,info))

    def test_true_qubit_shared_120_seeds_saturates_then_survives_flip(self):
        # Aligned measurements of two antipodal poles and an equatorial trine;
        # shared permutations of the five labels produce a rank-five average.
        def val(i,j):
            if i == j:
                return F(1)
            if max(i,j) < 2:
                return F(0)
            return F(1,4) if min(i,j) >= 2 else F(1,2)

        seeds = list(permutations(range(5)))
        self.assertEqual(len(seeds),120)
        probs = [[sum(val(s[i],s[j]) for s in seeds)/120 for j in range(5)] for i in range(5)]
        self.assertTrue(all(p == (1 if i==j else F(3,8)) for i,r in enumerate(probs)
                            for j,p in enumerate(r)))
        # Nonzero eigenvalues 5/8 and 5/2 (> D^2 rank without the shared seed).
        c, info = evaluate(spec(probs))
        self.assertEqual((c.status,c.witness,info["scaled_upper_gap"]),("inconclusive",None,"0"))
        noisy = [[F(1,25)+F(23,25)*p for p in r] for r in probs]
        c, info = evaluate(spec(box(noisy,F(1,100))))
        self.assertEqual(c.status,"inconclusive")
        self.assertGreater(F(info["scaled_upper_gap"]),0)

        # Six pure axial qubit states (+/- each Bloch axis) sum to zero.
        # From each axis state the five OTHER aligned effects have rates
        # 0,1/2,1/2,1/2,1/2. A common random permutation gives 2/5.
        # This tight real qubit is falsely rejected by rounding DOWN.
        six = [[F(1) if i==j else F(2,5) for j in range(6)] for i in range(6)]
        grid = adapter.SCALE
        self.assertLess(2*(6+30*F((2*grid)//5,grid)),36)
        c,info = evaluate(spec(six))
        self.assertEqual(c.status,"inconclusive")
        self.assertGreater(F(info["scaled_upper_gap"]),0)

    def test_binary_only_and_shared_classical_multivalued_trap(self):
        # A genuine bit + shared random label l; (l,[i==l]) has six outcomes.
        # Erroneous squared six-outcome affinity would give D >= 27/11 > 2.
        vectors = [[F(int(int(i==l)==b),3) for l,b in product(range(3),(0,1))] for i in range(3)]
        wrong = 9/sum(sum(F(1,3) for p,q in zip(a,b) if p and q)**2 for a in vectors for b in vectors)
        self.assertEqual(wrong,F(27,11))
        bad = spec([[0],[1],[0]],model="classical")
        bad["intervals"] = [[[str(p) for p in row]] for row in vectors]
        with self.assertRaises(ValueError):
            adapter.parse_binary_overlap_cut(bad)
        bad = spec(vectors,model="classical")
        bad["outcomes"] = ["a","b","c","d","e","f"]
        with self.assertRaises(ValueError):
            adapter.parse_binary_overlap_cut(bad)
        # Treat each coarse-grained indicator as a legitimate binary setting.
        c,_ = evaluate(spec(vectors,model="classical"))
        self.assertEqual(c.status,"inconclusive")

    def test_rectangular_bit_code_identical_orthogonal_and_ratio(self):
        bits = [[(i>>y)&1 for y in range(3)] for i in range(5)]
        for mode in ("classical","quantum"):
            for shared in (True,False):
                for basis in ("unconditional","joint_accepted_event"):
                    c,info = evaluate(spec(bits,dim=4,model=mode,basis=basis,seed=shared))
                    self.assertEqual(c.status,"counterexample")
                    self.assertEqual((info["ordered_overlap_sum_upper"], c.witness["actual"]),("5","-5"))
        c,info = evaluate(spec(bits,dim=4,basis="accepted_only"))
        self.assertEqual((c.status,c.checked,c.planned,c.witness),("unsupported",0,0,None))
        c,info = evaluate(spec([[0],[0],[0]],dim=1))
        self.assertEqual((c.status,info["scaled_upper_gap"]),("inconclusive","0"))
        c,info = evaluate(spec([[0],[1]],dim=1))
        self.assertEqual((c.status,info["scaled_upper_gap"]),("counterexample","-2"))
        c,_ = evaluate(spec([[0],[1]],dim=2))
        self.assertEqual((c.status,c.planned),("inconclusive",0))
        c,info = evaluate(spec([[F(1,2)],[F(500000000000,999999999999)]],dim=1))
        self.assertEqual((c.status,c.witness,info["scaled_upper_gap"]),("inconclusive",None,"0"))

    def test_partial_budget_or_deadline_has_no_verdict(self):
        raw = spec([[int(i==j) for j in range(5)] for i in range(5)],dim=4)
        c,details = evaluate(raw,max_cases=9)
        self.assertEqual((c.status,c.checked,c.planned,c.witness),("inconclusive",9,10,None))
        self.assertEqual((details["scaled_upper_gap"],details["stop_reason"]),(None,"max_cases"))
        with patch.object(adapter,"monotonic",side_effect=[0]*8+[20]*100):
            c,details=evaluate(raw,deadline=10)
        self.assertEqual((c.status,c.checked,c.witness,details["stop_reason"]),
                         ("inconclusive",1,None,"deadline"))
        for bad in (True,"never",float("nan"),float("inf")):
            with self.assertRaises(ValueError):
                evaluate(raw,deadline=bad)

    def test_schema_bounds_no_aliasing_and_no_oversize_artifact(self):
        raw = spec([[0],[1]],dim=1)
        raw["intervals"][0][0]=["00","0/2"]
        saved=copy.deepcopy(raw)
        obj=adapter.parse_binary_overlap_cut(raw)
        self.assertEqual(saved,raw)
        raw["intervals"][0][0][1]="1"
        self.assertEqual(obj.specification(),spec([[0],[1]],dim=1))
        self.assertEqual(adapter.LOADED_SOURCE_SHA256,hashlib.sha256(Path(adapter.__file__).read_bytes()).hexdigest())
        for key,value in (("family","prepare_measure_cut"),("intervals",[[["0","0"]],[]]),
                          ("intervals",[[["0","1/1000000000000"]]]*2),
                          ("intervals",[[["1/2","1/3"]]]*2),("intervals",[[[0,1]]]*2),
                          ("intervals",[[["0","1"]]*25]*2),("intervals",[[["0","1"]]]*25),
                          ("event",["x","y","z"])):
            with self.subTest(key=key),self.assertRaises((TypeError,ValueError)):
                adapter.parse_binary_overlap_cut({**raw,key:value})
        for kw in ({"dimension":True},{"intervals":((("0","1"),),)*2},{"shared_classical_seed":1}):
            with self.assertRaises(ValueError):
                replace(obj,**kw)
        # Full 24x24 supported table including a complete pair certificate.
        n=adapter.MAX_SETTINGS
        wide = spec([[F(1) if i==j else F(1,999999999999-i*n-j)
                      for j in range(n)] for i in range(n)],dim=n-1)
        c,info=evaluate(wide)
        self.assertEqual((c.status,c.checked),("counterexample",276))
        payload=json.dumps([wide,asdict(c),info]).encode()
        self.assertLess(len(payload),512*1024)


if __name__ == "__main__":
    unittest.main()
