"""Build two small experimental menus from genuinely different predictor families.

No synthetic outcome is treated as evidence. We request every predictor's
own counters using a dummy reference; only its predicted fields are used.
Acquisition costs are declared bookkeeping units, not time measurements.
"""

from __future__ import annotations

import json
import sys
from functools import cache
from itertools import combinations
from pathlib import Path

if not __package__:
    sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
from theory_experiments.discrimination_design import plan_design
from theory_experiments.primitive_screen import Limits
from theory_experiments.signed_contact_stream import (
    evaluate_signed_contact_stream,
    parse_signed_contact_stream,
)
from theory_experiments.ternary_network_nulls import (
    evaluate_ternary_network_nulls,
    parse_ternary_network_nulls,
)

SCHEMA = "idt-measurement-design/1"
H, G = (0,1,2), (1,2,3)


def need(ok, message):
    if not ok:
        raise ValueError(message)


def network_design():
    models = {"mobile":("mobile_depth", None), "stock":("stationary_bucket", None),
              "wire":("idle_wire", None), **{f"F{p}":("residue_field", p) for p in (2,5,7,11,101)}}
    tests = []
    for k in (1,2,3,4,5,6,7,8,9):
        for port in (0,3):
            allows = {}
            for model,(rule,modulus) in models.items():
                spec = {"id":"request", "family":"ternary_network_nulls", "rule":rule, "modulus":modulus,
                        "initial":[1,0,0,0], "contacts":[list(h) for h in (H,G)*k],
                        "readouts":[{"after":2*k, "port":port, "dark":False}]}
                _, details = evaluate_ternary_network_nulls(parse_ternary_network_nulls(spec),Limits(max_cases=96))
                dark = details["comparisons"][0]["predicted_dark"]
                need(type(dark) is bool and details["contacts_consumed"]==2*k, "incomplete prediction")
                allows[model] = ["dark" if dark else "bright"]
            tests.append({"id":f"block{k:02d}_port{port}","cost":2*k+1,
                          "outcomes":["bright","dark"], "allows":allows})
    return {"schema":SCHEMA,"models":[*models,"unmodeled"],"tests":tests}


def stream_design():
    models = {"bucket":"anonymous_bucket","rotor":"ordered_pair_rotor","wire":"idle_wire"}
    # Each query is a fresh three-port experiment. The unobserved initial
    # phase is allowed to vary across trials, not within one pulse sequence.
    menus = (("first_net_is_one",1,4,lambda v:sum(v)==1),
             ("first_source_zero",1,2,lambda v:v[0]==0),
             ("second_source_zero",2,3,lambda v:v[0]==0),
             ("cycle_source_negative",3,4,lambda v:v[0]<0),
             ("cycle_net_is_three",3,6,lambda v:sum(v)==3))
    tests = []
    for name,k,cost,response in menus:
        allowed = {}
        for model,rule in models.items():
            possible = set()
            for phase in range(1 if model=="wire" else 3):
                spec = {"id":"request","family":"signed_contact_stream","ports":3,"rule":rule,
                        "initial_phase":phase,"inputs":[{"port":0,"sign":1} for _ in range(k)],
                        "readouts":[{"after":k,"scope":"prefix","counts":[0,0,0]}]}
                _, details = evaluate_signed_contact_stream(parse_signed_contact_stream(spec),Limits(max_cases=16))
                need(details["inputs_consumed"]==k, "incomplete prediction")
                possible.add("yes" if response(details["comparisons"][0]["predicted_counts"]) else "no")
            allowed[model] = sorted(possible)
        tests.append({"id":name,"cost":cost,"outcomes":["no","yes"],"allows":allowed})
    return {"schema":SCHEMA,"models":[*models,"unmodeled"],"tests":tests}


def summarize(spec):
    plan = plan_design(spec)
    need(plan["status"] == "optimal", "search budget insufficient")
    leaves = [n["survivors"] for n in plan["nodes"].values() if n["test"] is None]
    need(all("unmodeled" in s for s in leaves), "unknown hypothesis was discarded")
    fixed_cost,fixed_tests = fixed_panel(spec)
    return {"worst_cost":plan["worst_cost"],"all_tests_cost":sum(t["cost"] for t in spec["tests"]),
            "optimal_fixed_cost":fixed_cost,"optimal_fixed_tests":fixed_tests,
            "root_test":plan["nodes"][plan["root"]]["test"],"retained_terminal_sets":sorted(leaves),
            "unseparable_pairs":plan["unseparable_pairs"]}


def fixed_panel(spec):
    """Exact pair-cover comparator for the two small preset menus only."""
    pairs = tuple(combinations(spec["models"],2))
    covers=[]
    for test in spec["tests"]:
        supports = {m:set(test["allows"].get(m) or test["outcomes"]) for m in spec["models"]}
        mask=sum(1<<i for i,(a,b) in enumerate(pairs) if supports[a].isdisjoint(supports[b]))
        covers.append((test["id"],test["cost"],mask))
    full=0
    for _,_,mask in covers:
        full |= mask

    @cache
    def solve(left):
        if not left:
            return 0,()
        bit=left & -left
        choices=[]
        for test_id,cost,mask in covers:
            if bit&mask:
                later,rest=solve(left & ~mask)
                choices.append((cost+later,tuple(sorted((test_id,*rest)))))
        return min(choices)

    return solve(full)


def probe():
    models = {key:summarize(f()) for key,f in (("network",network_design),("stream",stream_design))}
    return {"menus":models,"scope":"optimal for listed fresh interventions and units only; predictions are not measurements",
            "missing":"A model with no supplied prediction is kept in every terminal set."}


if __name__ == "__main__":
    print(json.dumps(probe(), sort_keys=True))
