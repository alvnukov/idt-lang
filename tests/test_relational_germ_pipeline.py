"""Request binding, offline route receipts and truly warm same-process reads."""

import copy
import hashlib
import json
import tempfile
import unittest
from itertools import product
from pathlib import Path
from unittest.mock import patch

from tests.test_relational_germ_observer import PASS, cube, replay, spec
from theory_experiments import candidate_pipeline as pipeline
from theory_experiments.primitive_screen import Limits, canonical_json
from theory_experiments.relational_germ_observer import (
    FLAT_CHECK_ID, TALLY_CHECK_ID, SCOPE, RelationalGermObserver,
)
from theory_experiments.source_candidate import SourceSnapshot, sha256_text

PINS=("theory_experiments/relational_germ_observer.py","theory_experiments/primitive_screen.py")


def shrikhande():
    delta=((1,0),(-1,0),(0,1),(0,-1),(1,1),(-1,-1))
    return [sorted(4*((x+a)%4)+(y+b)%4 for a,b in delta) for x,y in product(range(4),repeat=2)]


class RelationalGermPipelineTests(unittest.TestCase):
    def setUp(self):
        pipeline._verified_germ_body_digest.cache_clear()
        self.addCleanup(pipeline._verified_germ_body_digest.cache_clear)

    def test_native_predictions_and_scope_do_not_leak_into_archived_sources(self):
        g=cube(5,True)
        samples=[spec(g,refs=[(3,6,6)]),spec(g,refs=[(3,5,5)]),spec(g,same=True,diff=False),
                 spec([[1,2],[2,0],[1,0]],(0,1,2)),spec(shrikhande(),(0,1,2),False,False)]
        yes,bad,conflict,undefined,nonflat_germ=pipeline.run_batch(samples)
        self.assertEqual([r.report["status"] for r in (yes,bad,conflict,undefined,nonflat_germ)],
                         [PASS,"counterexample","counterexample","unsupported",PASS])
        self.assertEqual(yes.report["scope"]["reference_comparisons"][0]["tally"],6)
        self.assertEqual(nonflat_germ.report["scope"]["multiple_germs_at_vertex_in_completed_closures"],96)
        self.assertTrue(nonflat_germ.report["scope"]["endpoint_bit_path_independent"])
        for r in (yes,bad,conflict,undefined,nonflat_germ):
            self.assertEqual([c["id"] for c in r.report["checks"]],[FLAT_CHECK_ID,TALLY_CHECK_ID])
            self.assertEqual(r.report["rejection_scope"],SCOPE)
            self.assertEqual(r.report["evidence_kind"],"finite_local_germ_transport_and_submitted_tally_comparison_only")
            self.assertEqual((r.report["proof_status"],r.report["empirical_status"],
                              r.report["scope"]["scientific_status"]),("not_attempted","not_tested","unassessed"))
        x=conflict.report["checks"][0]["witness"]["inputs"]
        self.assertEqual({replay(g,x["root_germ"],path,True,False)[1] for path in x["routes"]},{0,1})
        self.assertTrue(all(path[0]==0 and path[-1]==x["endpoint"] for path in x["routes"]))
        self.assertEqual(undefined.report["scope"]["local_domain_issue"]["fourth_corner_candidates"],[])
        limited,=pipeline.run_batch([samples[2]],Limits(max_cases=159))
        self.assertEqual(limited.report["status"],"inconclusive")
        self.assertTrue(all(c["witness"] is None for c in limited.report["checks"]))
        body="-- no raw graph included\n"
        retained={"id":"no_graph","family":"source_theory","role":"primitive_base",
                  "components":["relational_germ_observer"],"declared_status":"unassessed",
                  "missing_bridges":["an independently submitted operational graph"],
                  "sources":[SourceSnapshot("Proofs/Example.lean",1,1,sha256_text(body),body).specification()]}
        with patch.object(pipeline,"evaluate_relational_germ_observer",side_effect=AssertionError("implicit graph")):
            saved,=pipeline.run_batch([retained])
            self.assertEqual(saved.report["status"],"unsupported")
            self.assertEqual(saved.report["scope"]["adapter_status"],"missing")

    def test_exact_request_budget_class_and_normalization(self):
        raw=spec(cube(5,True),refs=[(3,6,6),(0,0,0)])
        for row in raw["adjacency"]:
            row.reverse()
        parsed=pipeline.parse_hypothesis(raw)
        other=pipeline.parse_hypothesis(spec(cube(5,True),same=True))
        class Subclass(RelationalGermObserver):
            pass
        class OtherLimits(Limits):
            pass
        child=Subclass(**vars(parsed))
        budget=Limits()
        sources=pipeline.provenance()
        request=pipeline.request_for(parsed,budget,sources)
        legacy=pipeline.controls()["qm_born"]
        with patch.object(pipeline,"evaluate_relational_germ_observer",side_effect=AssertionError("unbound evaluation")):
            for obj,target in ((child,parsed),(parsed,legacy),(legacy,parsed),(parsed,other),(other,parsed)):
                with self.assertRaisesRegex(ValueError,"relational germ candidate/limits"):
                    pipeline.compute(obj,budget,pipeline.request_for(target,budget,sources))
            for lim in (OtherLimits(),Limits(max_cases=2)):
                with self.assertRaisesRegex(ValueError,"relational germ candidate/limits"):
                    pipeline.compute(parsed,lim,request)
            bad=copy.deepcopy(request)
            bad["candidate"]=raw
            with self.assertRaisesRegex(ValueError,"relational germ candidate/limits"):
                pipeline.compute(parsed,budget,bad)
            bad=copy.deepcopy(request)
            bad["limits"]["max_copies"]=True
            with self.assertRaisesRegex(ValueError,"relational germ candidate/limits"):
                pipeline.compute(parsed,budget,bad)
        with tempfile.TemporaryDirectory() as tmp:
            cache=Path(tmp)
            first,=pipeline.run_batch([raw],cache_dir=cache)
            norm,=pipeline.run_batch([parsed.specification()],cache_dir=cache)
            self.assertEqual(first.key,norm.key)
            self.assertTrue(norm.reused)
            with self.assertRaisesRegex(ValueError,"relational germ candidate/limits"):
                pipeline.run_batch([raw],OtherLimits(),cache)

    def test_pins_for_loaded_checker_and_shared_helpers_on_known_warm_body(self):
        raw=spec(cube(5,True))
        original=Path.read_bytes
        with tempfile.TemporaryDirectory() as tmp:
            root=Path(tmp)
            r,=pipeline.run_batch([raw],cache_dir=root)
            obj=pipeline.parse_hypothesis(raw)
            req=r.report["request"]
            for path in PINS:
                target=pipeline.ROOT/path
                contents=original(target)
                self.assertEqual(req["provenance"]["source_sha256"][path],
                                 hashlib.sha256(contents).hexdigest())
                bad=copy.deepcopy(req)
                bad["provenance"]["source_sha256"][path]="0"*64
                for action in (lambda: pipeline.compute(obj,Limits(),bad),lambda: pipeline.read_entry(r.artifact,bad)):
                    with self.assertRaisesRegex(ValueError,"relational germ source changed"):
                        action()
                def altered(file):
                    return contents+b"\n# different checkout" if file==target else original(file)
                with patch.object(Path,"read_bytes",altered):
                    current=pipeline.provenance()["source_sha256"]
                    with patch.object(pipeline,"LOADED_SOURCE_HASHES", current):
                        for action in (lambda: pipeline.run_batch([raw],cache_dir=root),
                                       lambda: pipeline.run_batch([raw],cache_dir=root/"missing"),
                                       lambda: pipeline.read_entry(r.artifact,req),
                                       lambda: pipeline.compute(obj,Limits(),req),
                                       lambda: pipeline.replay_artifact(r.artifact)):
                            with self.subTest(path=path),self.assertRaisesRegex(ValueError,"relational germ source changed"):
                                action()
            self.assertFalse((root/"missing").exists())

    def test_rehashed_false_paths_status_scope_swapped_and_truncated_reports(self):
        g=cube(5,True)
        raw=spec(g,same=True,diff=False)
        with tempfile.TemporaryDirectory() as tmp:
            cache=Path(tmp)
            conflict,=pipeline.run_batch([raw],Limits(max_cases=160),cache)
            limited,=pipeline.run_batch([raw],Limits(max_cases=159),cache)
            undef,=pipeline.run_batch([spec([[1,2],[0,2],[0,1]],(0,1,2))],cache_dir=cache)
            req=conflict.report["request"]
            with self.assertRaisesRegex(ValueError,"cache integrity/request mismatch"):
                pipeline.read_entry(limited.artifact,req)
            original=conflict.artifact.read_bytes()
            # Mutating the object the caller received cannot mutate the
            # verified cache's immutable digest or a future file-backed result.
            conflict.report["checks"][0]["witness"]["inputs"]["routes"][0][0]=31
            with patch.object(pipeline,"evaluate_relational_germ_observer",side_effect=AssertionError("warm traversal")):
                intact=pipeline.read_entry(conflict.artifact,req)
                self.assertEqual(intact["checks"][0]["witness"]["inputs"]["routes"][0][0],0)
                with self.assertRaisesRegex(ValueError,"cached relational germ verdict/routes"):
                    pipeline.publish(cache/"reject.json",conflict.report,req)
            self.assertFalse((cache/"reject.json").exists())
            row=json.loads(original)
            row["report"]["checks"][0]["witness"]["inputs"]["routes"][0][0]=31
            row["report_sha256"]=pipeline.digest(row["report"])
            tampered=canonical_json(row).encode()
            conflict.artifact.write_bytes(tampered)
            for cold in (False,True):
                if cold:
                    pipeline._verified_germ_body_digest.cache_clear()
                for action in (lambda: pipeline.read_entry(conflict.artifact,req),
                               lambda: pipeline.run_batch([raw],Limits(max_cases=160),cache),
                               lambda: pipeline.replay_artifact(conflict.artifact)):
                    with self.assertRaisesRegex(ValueError,"cached relational germ verdict/routes"):
                        action()
            self.assertEqual(conflict.artifact.read_bytes(),tampered)
            for item in (limited,undef):
                for path,new in ((("status",),"counterexample"),(("scope","scientific_status"),"proved"),
                                 (("empirical_status",),"observed"),(("scope","reference_comparisons"),[{"tally":6}])):
                    changed=copy.deepcopy(item.report)
                    dest=changed
                    for part in path[:-1]:
                        dest=dest[part]
                    dest[path[-1]]=new
                    with self.assertRaisesRegex(ValueError,"cached relational germ verdict/routes"):
                        pipeline.publish(cache/"reject.json",changed,changed["request"])
                    self.assertFalse((cache/"reject.json").exists())

    def test_large_receipt_unknown_disk_rechecked_once_explicit_fresh_and_replay_recompute(self):
        # 32 vertices, seven incident germs, multiple transported directions,
        # 32 submitted endpoint intervals; no coordinates in the receipt.
        h=shrikhande()
        g=[[16*z+n for n in h[v]]+[16*(1-z)+v] for z in (0,1) for v in range(16)]
        raw=spec(g,(0,1,2),False,False,[(v,-10**6,10**6) for v in range(32)])
        backend=pipeline.evaluate_relational_germ_observer
        with tempfile.TemporaryDirectory() as tmp:
            cache=Path(tmp)
            r,=pipeline.run_batch([raw],cache_dir=cache)
            pristine=r.artifact.read_bytes()
            self.assertLess(len(pristine),512*1024)
            self.assertLess(len(canonical_json(raw).encode()),128*1024)
            self.assertEqual(r.report["status"],PASS)
            pipeline._verified_germ_body_digest.cache_clear()  # simulate unfamiliar on-disk receipt
            with patch.object(pipeline,"evaluate_relational_germ_observer",wraps=backend) as calculations:
                with patch.object(pipeline,"compute",side_effect=AssertionError("warm pipeline recomputed")):
                    for expected_calls in (1,1):
                        w,=pipeline.run_batch([raw],cache_dir=cache)
                        self.assertTrue(w.reused)
                        self.assertEqual(w.report,r.report)
                        self.assertEqual(calculations.call_count,expected_calls)
                again,=pipeline.run_batch([raw],cache_dir=cache,fresh=True)
                self.assertFalse(again.reused)
                self.assertEqual(calculations.call_count,2)
                self.assertEqual(pipeline.replay_artifact(r.artifact),r.report)
                self.assertEqual(calculations.call_count,3)
            self.assertEqual(r.artifact.read_bytes(),pristine)
            self.assertEqual(pipeline._verified_germ_body_digest.cache_info().maxsize,128)
            r.artifact.write_bytes(pristine+b" "*(512*1024+1-len(pristine)))
            with self.assertRaisesRegex(ValueError,"exceeds 512 KiB"):
                pipeline.read_entry(r.artifact,r.report["request"])
            with self.assertRaisesRegex(ValueError,"exceeds 512 KiB"):
                pipeline.replay_artifact(r.artifact)


if __name__=="__main__":
    unittest.main()
