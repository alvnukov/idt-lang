"""Choose the cheapest worst-case next readout; never edit a submission or baseline."""

from __future__ import annotations

import argparse
import json
import sys
from pathlib import Path

if not __package__:
    sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
from scripts.probe_active_readout_panels import network_design, stream_design
from theory_experiments.discrimination_design import plan_design


def follow(plan, labels):
    if plan["status"] != "optimal":
        if labels:
            raise ValueError("no certified plan to follow")
        return {"status":plan["status"],"next_test":None,"survivors":plan["models"]}
    state = plan["root"]
    for index,label in enumerate(labels):
        node = plan["nodes"][state]
        if node["test"] is None:
            raise ValueError("too many observations: the plan has already stopped")
        if label not in node["children"]:
            raise ValueError(f"unexpected label for {node['test']}: {label}")
        state = node["children"][label]
        if state is None:
            if index+1 != len(labels):
                raise ValueError("too many observations: the outcome already left the submitted library")
            return {"status":"outside_submitted_library","next_test":None,"survivors":[]}
    node = plan["nodes"][state]
    return {"status":"terminal" if node["test"] is None else "awaiting_observation",
            "next_test":node["test"],"survivors":node["survivors"],
            "remaining_worst_cost":node["worst_cost"],"declared_labels":sorted(node["children"]),
            "outside_library_labels":sorted(k for k,v in node["children"].items() if v is None)}


def _object(pairs):
    out = {}
    for k,v in pairs:
        if k in out:
            raise ValueError(f"duplicate JSON key: {k}")
        out[k] = v
    return out


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    src = parser.add_mutually_exclusive_group(required=True)
    src.add_argument("--spec",type=Path,help="independent finite prediction supports in JSON")
    src.add_argument("--demo",choices=("network","stream"),help="compute a menu from a typed finite predictor")
    parser.add_argument("--state-budget",type=int,default=20000)
    parser.add_argument("--outcome",action="append",default=[],help="observed label, in adaptive order")
    parser.add_argument("--full",action="store_true",help="also return the full certified decision graph")
    args = parser.parse_args()
    try:
        if args.spec:
            with args.spec.open("rb") as file:
                data = file.read(262145)
            if len(data)>262144:
                raise ValueError("spec exceeds 256 KiB")
            spec = json.loads(data.decode("utf-8"),object_pairs_hook=_object)
        else:
            spec = (network_design if args.demo=="network" else stream_design)()
        design = plan_design(spec,state_budget=args.state_budget)
        output = {"design_status":design["status"], "worst_cost":design["worst_cost"],
                  "unseparable_pairs":design["unseparable_pairs"],"current":follow(design,args.outcome),
                  "scope":"listed fresh preparations and cost units only; no history or physics statuses changed"}
        if args.full:
            output["plan"] = design
        print(json.dumps(output,sort_keys=True))
        return 0 if design["status"]=="optimal" else 2
    except (ValueError,OSError,UnicodeError,RecursionError) as exc:
        parser.exit(2,f"plan_candidate_readouts: {exc}\n")


if __name__ == "__main__":
    raise SystemExit(main())
