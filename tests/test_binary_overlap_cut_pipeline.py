"""Bounded binary-overlap receipts, exact request binding and verified warm reads."""

import copy
import hashlib
import json
import tempfile
import unittest
from fractions import Fraction as F
from pathlib import Path
from unittest.mock import patch

from theory_experiments import candidate_pipeline as pipeline
from theory_experiments.binary_overlap_cut import CHECK_ID, SCOPE, BinaryOverlapCut
from theory_experiments.prepare_measure_cut import RANK_CHECK_ID, TRACE_CHECK_ID
from theory_experiments.primitive_screen import Limits, canonical_json
from theory_experiments.source_candidate import SourceSnapshot, sha256_text

PINS = ("theory_experiments/binary_overlap_cut.py", "theory_experiments/prepare_measure_cut.py",
        "theory_experiments/primitive_screen.py")


def spec(table=None, *, dim=2, basis="unconditional", seed=True, family="binary_overlap_cut"):
    if table is None:
        table = [[int(i == j) for j in range(3)] for i in range(3)]
    def cell(v):
        a,b = v if type(v) is tuple else (v,v)
        return [str(a),str(b)]
    return {"id":"cut_table","family":family,"event":"ref","event_basis":basis,
            "memory":{"model":"quantum","dimension":dim,"shared_classical_seed":seed},
            "intervals":[[cell(v) for v in row] for row in table]}


class BinaryOverlapPipelineTests(unittest.TestCase):
    def test_distinct_family_and_seed_controls(self):
        table = [[F(1,1+36*(i-j)**2) for j in range(5)] for i in range(5)]
        noisy = [[(max(0,v-F(39,4000)),min(1,v+F(39,4000))) for v in row] for row in table]
        qubit = [[1 if i==j else F(3,8) for j in range(5)] for i in range(5)]
        samples = [spec(noisy, dim=4), spec(noisy, dim=4, seed=False),
                   spec(noisy, dim=4, basis="joint_accepted_event"),
                   spec(noisy, dim=4, basis="accepted_only"), spec(noisy, dim=5), spec(qubit)]
        old = spec(noisy, dim=4, family="prepare_measure_cut")
        results = pipeline.run_batch([*samples,old])
        self.assertEqual([r.report["status"] for r in results],
                         ["counterexample"]*3+["unsupported","inconclusive","inconclusive","inconclusive"])
        for raw,r in zip(samples,results):
            self.assertEqual(r.report["request"]["candidate"],raw)
            self.assertEqual([c["id"] for c in r.report["checks"]],[CHECK_ID])
            self.assertEqual(r.report["rejection_scope"],SCOPE)
            self.assertEqual(r.report["evidence_kind"],"necessary_binary_overlap_bounds_on_submitted_event_table_only")
            self.assertEqual(r.report["proof_status"],"not_attempted")
            self.assertEqual(r.report["empirical_status"],"not_tested")
            self.assertTrue(r.report["scope"]["necessary_conditions_only"])
        old_report = results[-1].report
        self.assertEqual([c["id"] for c in old_report["checks"]],[RANK_CHECK_ID, TRACE_CHECK_ID])
        self.assertEqual(old_report["evidence_kind"],"necessary_conditions_on_submitted_finite_table_only")
        self.assertNotEqual(old_report["rejection_scope"],SCOPE)
        self.assertEqual(len({r.key for r in results}),len(results))

    def test_exact_binding_before_evaluation_and_source_not_a_table(self):
        cut = pipeline.parse_hypothesis(spec())
        class OtherCut(BinaryOverlapCut):
            pass
        class OtherLimits(Limits):
            pass
        child = OtherCut(**vars(cut))
        old = pipeline.parse_hypothesis(spec(family="prepare_measure_cut"))
        alt = pipeline.parse_hypothesis(spec(basis="accepted_only"))
        sources, bounds = pipeline.provenance(), Limits()
        request = pipeline.request_for(cut,bounds,sources)
        with patch.object(pipeline,"evaluate_binary_overlap_cut",side_effect=AssertionError("unbound evaluation")):
            for actual,target in ((cut,old),(old,cut),(cut,alt),(alt,cut),(child,cut)):
                with self.assertRaisesRegex(ValueError,"binary overlap cut candidate/limits"):
                    pipeline.compute(actual,bounds,pipeline.request_for(target,bounds,sources))
            for invalid in (OtherLimits(),Limits(max_cases=1)):
                with self.assertRaisesRegex(ValueError,"binary overlap cut candidate/limits"):
                    pipeline.compute(cut,invalid,request)
            wrong = copy.deepcopy(request)
            wrong["limits"]["coefficient_radius"]=True
            with self.assertRaisesRegex(ValueError,"binary overlap cut candidate/limits"):
                pipeline.compute(cut,bounds,wrong)
            body = "-- binary_overlap_cut is not a derived prediction\n"
            retained = {"id":"not_a_table","family":"source_theory","role":"primitive_base",
                        "components":["binary_overlap_cut"],"declared_status":"unassessed",
                        "missing_bridges":["an actionable prediction adapter"],
                        "sources":[SourceSnapshot("Proofs/Cut.lean",1,1,sha256_text(body),body).specification()]}
            result, = pipeline.run_batch([retained])
            self.assertEqual((result.report["status"],result.report["scope"]["adapter_status"]),
                             ("unsupported","missing"))

    def test_actual_loaded_source_hashes_for_all_three_dependencies(self):
        raw, original_read = spec(), Path.read_bytes
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            baseline, = pipeline.run_batch([raw],cache_dir=root)
            request = baseline.report["request"]
            candidate = pipeline.parse_hypothesis(raw)
            for relative in PINS:
                target = pipeline.ROOT / relative
                actual = original_read(target)
                self.assertEqual(request["provenance"]["source_sha256"][relative],hashlib.sha256(actual).hexdigest())
                forged=copy.deepcopy(request)
                forged["provenance"]["source_sha256"][relative]="0"*64
                for action in (lambda: pipeline.compute(candidate,Limits(),forged),
                               lambda: pipeline.read_entry(baseline.artifact,forged)):
                    with self.subTest(path=relative),self.assertRaisesRegex(ValueError,"binary overlap cut source changed"):
                        action()
                def changed(p):
                    return actual+b"\n# test newer disk image\n" if p==target else original_read(p)
                with patch.object(Path,"read_bytes",changed):
                    newer=pipeline.provenance()["source_sha256"]
                    with patch.object(pipeline,"LOADED_SOURCE_HASHES",newer):
                        for action in (lambda: pipeline.run_batch([raw],cache_dir=root/"missing"),
                                       lambda: pipeline.run_batch([raw],cache_dir=root),
                                       lambda: pipeline.compute(candidate,Limits(),request),
                                       lambda: pipeline.read_entry(baseline.artifact,request),
                                       lambda: pipeline.replay_artifact(baseline.artifact)):
                            with self.subTest(path=relative),self.assertRaisesRegex(ValueError,"binary overlap cut source changed"):
                                action()
            self.assertFalse((root/"missing").exists())

    def test_rehashed_promotions_and_changed_certificates_fail_before_reuse(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            good, limited = (pipeline.run_batch([spec()],Limits(max_cases=n),root)[0] for n in (3,2))
            self.assertEqual((good.report["status"],limited.report["status"]),("counterexample","inconclusive"))
            cases = [(good, ("checks",0,"witness","inputs","pair_certificate",0,1), 999),
                     (good, ("scope","scientific_status"), "confirmed"),
                     (good, ("empirical_status",), "measured"),
                     (good, ("checks",0,"status"), "no_counterexample_within_bounds"),
                     (limited, ("checks",0,"checked"), 3),
                     (limited, ("status",), "counterexample")]
            for r,path,value in cases:
                pristine = r.artifact.read_bytes()
                envelope = json.loads(pristine)
                container = envelope["report"]
                for key in path[:-1]:
                    container=container[key]
                container[path[-1]]=value
                envelope["report_sha256"]=pipeline.digest(envelope["report"])
                changed=canonical_json(envelope).encode()
                r.artifact.write_bytes(changed)
                bounds = Limits(max_cases=r.report["request"]["limits"]["max_cases"])
                fresh_path=root/"never-publish.json"
                for action in (lambda: pipeline.run_batch([spec()],bounds,root),
                               lambda: pipeline.read_entry(r.artifact,r.report["request"]),
                               lambda: pipeline.replay_artifact(r.artifact),
                               lambda: pipeline.publish(fresh_path,envelope["report"],r.report["request"])):
                    with self.subTest(path=path),self.assertRaisesRegex(ValueError,"cached binary overlap verdict/certificate"):
                        action()
                self.assertFalse(fresh_path.exists())
                self.assertEqual(r.artifact.read_bytes(),changed)
                r.artifact.write_bytes(pristine)
            # Even a self-consistent replacement of status/checks/witness/scope
            # by a real higher-budget report cannot relabel truncated work.
            bad = copy.deepcopy(good.report)
            bad["request"]=limited.report["request"]
            with self.assertRaisesRegex(ValueError,"cached binary overlap verdict/certificate"):
                pipeline.publish(root/"wrong.json",bad,bad["request"])

    def test_full_size_real_cache_replay_budget_and_512kib_limit(self):
        n=24
        raw=spec([[1 if i==j else F(1,999999999999-n*i-j) for j in range(n)] for i in range(n)],dim=n-1)
        with tempfile.TemporaryDirectory() as tmp:
            cache=Path(tmp)
            fresh,=pipeline.run_batch([raw],cache_dir=cache)
            self.assertEqual(fresh.report["checks"][0]["checked"],276)
            self.assertLess(fresh.artifact.stat().st_size,512*1024)
            pristine=fresh.artifact.read_bytes()
            with patch.object(pipeline,"compute",side_effect=AssertionError("warm hit invoked general compute")):
                warm,=pipeline.run_batch([raw],cache_dir=cache)
                self.assertTrue(warm.reused)
                self.assertEqual(warm.report,fresh.report)
                class OtherLimits(Limits):
                    pass
                with self.assertRaisesRegex(ValueError,"binary overlap cut candidate/limits"):
                    pipeline.run_batch([raw],OtherLimits(),cache)
            self.assertEqual(pipeline.replay_artifact(fresh.artifact),fresh.report)
            again,=pipeline.run_batch([raw],cache_dir=cache,fresh=True)
            self.assertFalse(again.reused)
            self.assertEqual(again.report,fresh.report)
            self.assertEqual(pristine,fresh.artifact.read_bytes())
            fresh.artifact.write_bytes(pristine+b" "*(512*1024+1-len(pristine)))
            with self.assertRaisesRegex(ValueError,"exceeds 512 KiB"):
                pipeline.read_entry(fresh.artifact,fresh.report["request"])
            with self.assertRaisesRegex(ValueError,"exceeds 512 KiB"):
                pipeline.replay_artifact(fresh.artifact)


if __name__ == "__main__":
    unittest.main()
