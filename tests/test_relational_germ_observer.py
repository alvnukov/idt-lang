"""Raw-square predictions versus independent coordinate and route-replay controls."""

import copy
import hashlib
import json
import tempfile
import unittest
from dataclasses import asdict, replace
from itertools import combinations, product
from pathlib import Path
from unittest.mock import patch

from theory_experiments import relational_germ_observer as adapter
from theory_experiments.primitive_screen import Limits, aggregate_status, load_json

PASS="no_counterexample_within_bounds"


def cube(n,fold=False):
    # Independent fixture only. No coordinates are passed to the evaluator.
    mask=(1<<n)-1
    def representative(v):
        return min(v,mask^v) if fold else v
    return [sorted(representative(i^(1<<k)) for k in range(n)) for i in range(1<<(n-int(fold)))]


def spec(g,route=(0,1,3),same=False,diff=True,refs=((0,0,0),)):
    return {"id":"germ","family":"relational_germ_observer","adjacency":g,"marked_route":list(route),
            "recorder":{"flip_on_same":same,"flip_on_different":diff},
            "references":[{"vertex":v,"lower":lo,"upper":hi} for v,lo,hi in refs]}


def evaluate(raw,budget=5000,**opts):
    c=adapter.parse_relational_germ_observer(raw)
    return adapter.evaluate_relational_germ_observer(c,Limits(max_cases=budget),**opts)


def folded_prediction(v):
    # Chosen two-turn 0->1->3. In this fixture b_j(v) is parity(v) XOR bit j:
    # unchanged on its own edge, complemented on every other edge. It is
    # invariant under the five-coordinate complement used only by this oracle.
    signs=[(v.bit_count()&1)^((v>>j)&1) for j in range(5)]
    return 5*(signs[0]+signs[1])-2*sum(signs)


def replay(g,origin,path,same,diff):
    p,bit=origin,0
    for i,j in zip(path,path[1:]):
        if p not in g[i] or j not in g[i]:
            raise ValueError("nonlocal path witness")
        if j==p:
            p,bit=i,bit^same
        else:
            candidates=[k for k in g[j] if k!=i and p in g[k]]
            if len(candidates)!=1:
                raise ValueError("invalid square on submitted route")
            p,bit=candidates[0],bit^diff
    return p,bit


class RelationalGermTests(unittest.TestCase):
    def test_every_folded_endpoint_against_independent_integer_predictions(self):
        g=cube(5,True)
        refs=[(v,folded_prediction(v),folded_prediction(v)) for v in range(16)]
        checks,d=evaluate(spec(g,refs=refs))
        self.assertEqual([c.status for c in checks],[PASS,PASS])
        self.assertEqual([c.checked for c in checks],[5,16])
        self.assertEqual(d["product_states_fully_expanded"],80)
        self.assertEqual(d["outgoing_transfers_examined"],400)
        for row in d["reference_comparisons"]:
            self.assertEqual(row["tally"],folded_prediction(row["vertex"]))
            self.assertEqual(row["tally"],row["plus"]-row["minus"])
            self.assertEqual(row["plus"]+row["minus"]+row["abstain"],10)
        self.assertEqual(set(q["tally"] for q in d["reference_comparisons"]),{-4,-3,0,1,2,6})
        self.assertEqual((d["scientific_status"],d["empirical_status"],d["proof_status"]),
                         ("unassessed","not_tested","not_attempted"))

    def test_folded_conflicts_witness_replays_unwrapped_all_four_are_flat(self):
        g=cube(5,True)
        for same,diff in product((False,True),repeat=2):
            checks,d=evaluate(spec(g,same=same,diff=diff))
            flat,tally=checks
            if same:
                self.assertEqual((flat.status,tally.status),("counterexample","unsupported"))
                x=flat.witness["inputs"]
                self.assertEqual(x["routes"][0][0],x["routes"][1][0])
                for route,bit in zip(x["routes"],x["final_bits"]):
                    self.assertEqual((route[0],route[-1]),(0,x["endpoint"]))
                    self.assertEqual(replay(g,x["root_germ"],route,same,diff)[1],bit)
                self.assertEqual(set(x["final_bits"]),{0,1})
                self.assertEqual(d["product_states_fully_expanded"],160)
            else:
                self.assertEqual((flat.status,tally.status),(PASS,PASS))
            checks,d=evaluate(spec(cube(5),same=same,diff=diff))
            self.assertEqual([c.status for c in checks],[PASS,PASS])
            self.assertTrue(d["endpoint_bit_path_independent"])

    def test_bad_reference_witness_and_renamed_unordered_ports(self):
        g=cube(5,True)
        refs=[(3,7,9),(0,0,0)]
        checks,d=evaluate(spec(g,refs=refs))
        self.assertEqual([c.status for c in checks],[PASS,"counterexample"])
        w=checks[1].witness
        a,b=w["inputs"]["mark_bits"],w["inputs"]["reference_bits"]
        self.assertEqual(sum((a[i]-a[j])*(b[i]-b[j]) for i,j in combinations(range(5),2)),6)
        self.assertEqual((w["actual"],w["inputs"]["tally"]),("-1",6))
        ren=[(5*i+7)%16 for i in range(16)]
        out=[None]*16
        for i,adj in enumerate(g):
            out[ren[i]]=[ren[j] for j in reversed(adj)]
        raw=spec(out,[ren[i] for i in (0,1,3)],refs=[(ren[v],lo,hi) for v,lo,hi in reversed(refs)])
        chk,dr=evaluate(raw)
        self.assertEqual([c.status for c in chk],[PASS,"counterexample"])
        retained=lambda row:(row["plus"],row["minus"],row["abstain"],row["tally"])
        self.assertEqual({ren[q["vertex"]]:retained(q) for q in d["reference_comparisons"]},
                         {q["vertex"]:retained(q) for q in dr["reference_comparisons"]})
        self.assertEqual(aggregate_status(chk),"counterexample")

    def test_undefined_squares_are_unsupported_not_holonomy(self):
        def rook(n):
            return [[v for v in range(n*n) if u!=v and (u//n==v//n or u%n==v%n)] for u in range(n*n)]
        for g,route,count in (([[1,2],[0,2],[0,1]],(0,1,2),0),(rook(5),(0,1,2),2)):
            checks,d=evaluate(spec(g,route,same=True,diff=True))
            self.assertEqual([c.status for c in checks],["unsupported"]*2)
            self.assertTrue(all(c.witness is None for c in checks))
            self.assertFalse(d["flat_bit_domain_complete"])
            x=d["local_domain_issue"]
            germ,_=replay(g,x["root_germ"],x["route_to_source"],True,True)
            u,p,v=x["source"],x["transported_germ"],x["cross_to"]
            self.assertEqual((x["route_to_source"][-1],germ),(u,p))
            self.assertEqual(sorted(set(g[p])&set(g[v])-{u}),x["fourth_corner_candidates"])
            self.assertEqual(len(x["fourth_corner_candidates"]),count)

    def test_nontrivial_direction_holonomy_does_not_reject_a_constant_bit(self):
        offsets=((1,0),(-1,0),(0,1),(0,-1),(1,1),(-1,-1))
        shr=[sorted(4*((x+i)%4)+(y+j)%4 for i,j in offsets) for x,y in product(range(4),repeat=2)]
        checks,d=evaluate(spec(shr,(0,1,2),False,False,[(i,0,0) for i in range(16)]))
        self.assertEqual([c.status for c in checks],[PASS,PASS])
        self.assertEqual(d["multiple_germs_at_vertex_in_completed_closures"],96)
        self.assertTrue(all(q["abstain"]==15 and q["tally"]==0 for q in d["reference_comparisons"]))
        checks,d=evaluate(spec(cube(2)+[[]],refs=[(4,-2,2)]))
        self.assertEqual([c.status for c in checks],[PASS,"unsupported"])
        self.assertEqual(d["unreachable_references"],[4])

    def test_partial_budget_and_deadline_do_not_promote_provisional_conflicts(self):
        raw=spec(cube(5,True),same=True,diff=False,refs=[(0,1,1)])
        for budget in (1,32,159):
            checks,d=evaluate(raw,budget)
            self.assertEqual([c.status for c in checks],["inconclusive"]*2)
            self.assertEqual(d["stop_reason"],"max_cases")
            self.assertEqual(d["product_states_fully_expanded"],budget)
            self.assertTrue(all(c.witness is None for c in checks))
        self.assertEqual(evaluate(raw,160)[0][0].status,"counterexample")
        with patch.object(adapter,"monotonic",side_effect=[0]*10+[5]*100):
            checks,d=evaluate(raw,deadline=5)
            self.assertEqual([c.status for c in checks],["inconclusive"]*2)
            self.assertEqual(d["stop_reason"],"deadline")
        for bad in (True,float("nan"),float("inf")):
            with self.assertRaises(ValueError):
                evaluate(raw,deadline=bad)

    def test_strict_schema_ownership_and_small_receipt(self):
        raw=spec(cube(3))
        c=adapter.parse_relational_germ_observer(raw)
        raw["adjacency"][0].clear()
        self.assertEqual(c.specification(),spec(cube(3)))
        self.assertEqual(adapter.LOADED_SOURCE_SHA256,hashlib.sha256(Path(adapter.__file__).read_bytes()).hexdigest())
        for key,val in (("marked_route",[0,1,0]),("marked_route",[0,3,1]),("marked_route",[True,1,3]),
                        ("references",[]),("references",[{"vertex":1,"lower":2,"upper":1}]),
                        ("references",[{"vertex":1,"lower":0,"upper":2}]*2),
                        ("recorder",{"flip_on_same":0,"flip_on_different":True}),
                        ("adjacency",[[1,1],[0,2],[1]]),("adjacency",[[1],[2],[1]])):
            with self.subTest(key=key),self.assertRaises(ValueError):
                adapter.parse_relational_germ_observer({**spec(cube(3)),key:val})
        with self.assertRaises(ValueError):
            replace(c,flip_on_same=1)
        invalid=copy.deepcopy(c.specification())
        invalid["coordinates"]=[0,1,2]
        with self.assertRaises(ValueError):
            adapter.parse_relational_germ_observer(invalid)
        largest=spec(cube(5),refs=[(v,-10**6,10**6) for v in range(32)])
        checks,details=evaluate(largest)
        self.assertLess(len(json.dumps(largest)),128*1024)
        self.assertLess(len(json.dumps([largest,list(map(asdict,checks)),details])),512*1024)
        with tempfile.NamedTemporaryFile() as file:
            file.write(b" "*(128*1024+1))
            file.flush()
            with self.assertRaisesRegex(ValueError,"128 KiB"):
                load_json(Path(file.name))


if __name__=="__main__":
    unittest.main()
