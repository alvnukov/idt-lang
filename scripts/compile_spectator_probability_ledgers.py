"""Submit comparators separately from assumptions, geometry and solver.

All trials below are synthetic designs. A link is an explicit asserted
equality/tolerance, not a result inferred by the feasibility engine. The
five-mode geometry and its native circuit/measurement identities are
independently checked by probe_five_mode_shadow_boundary. The ledger
must recover the inconsistency without any proposed final probabilities.
"""

from itertools import combinations


class Design:
    def __init__(self, name):
        self.data = {"id":name, "family":"operational_probability_ledger", "basis":"all_attempts",
                     "settings":[], "bounds":[], "links":[]}

    def setting(self, s, outcomes):
        self.data["settings"].append({"id":s, "outcomes":list(outcomes)})

    @staticmethod
    def event(s, *out):
        return {"setting":s,"outcomes":list(out)}

    def bound(self, e, val):
        self.data["bounds"].append({"event":e,"lower":val,"upper":val})

    def link(self, a, b, eps="0"):
        self.data["links"].append({"left":a,"right":b,"tolerance":eps})


def six(name, local, tolerance, *, free=False, conditioned=False):
    s = Design(name)
    s.setting("central", [f"p{i}" for i in range(6)])
    if conditioned:
        s.data["basis"] = "separately_postselected"
    for i in (0,1,3,4,5):
        t = f"local{i}"
        s.setting(t,["hit","miss"])
        e = s.event(t,"hit")
        s.bound(e,local)
        if not free:
            s.link(e,s.event("central",f"p{i}"),tolerance)
    return s.data


def five(name, fhalf, fsixth, gthird, *, omit_shared=False):
    s = Design(name)
    # Axis outputs of preparations A/D, their two balance refinements,
    # and the calibrated balanced-pair read on preparation K.
    for t,v in (("a","half"),("d","sixth")):
        s.setting(t,["zero",v,"other"])
        s.setting(t+"pair",["plus","minus","other"])
        s.bound(s.event(t,"zero"),"0")
        s.bound(s.event(t,v),fhalf if t=="a" else fsixth)
        s.link(s.event(t+"pair","plus"),s.event(t+"pair","minus"))
        s.link(s.event(t+"pair","plus","minus"),s.event(t,"zero",v))
    s.setting("kpair",["plus","other"])
    s.bound(s.event("kpair","plus"),gthird)
    for t in ("b","c"):
        s.setting(t,[f"p{i}" for i in range(5)])
    refs = {"zero":s.event("a","zero"),"half":s.event("apair","plus"),
            "sixth":s.event("dpair","plus"),"third":s.event("kpair","plus")}
    for t,i,j,p,m in [
        *(("b",i,j,"half","zero") for i,j in combinations((1,2,3),2)),
        ("c",1,2,"sixth","zero"),("c",1,3,"third","half"),("c",2,3,"third","half"),
    ]:
        pair = f"{t}pair{i}{j}"
        s.setting(pair,["plus","minus","other"])
        s.link(s.event(pair,"plus"),refs[p])
        s.link(s.event(pair,"minus"),refs[m])
        if not (omit_shared and t=="c"):
            s.link(s.event(t,f"p{i}",f"p{j}"),s.event(pair,"plus","minus"))
    for t in ("b","c"):
        s.link(s.event(t,"p4"),s.event("a","half"))
    s.link(s.event("c","p0"),s.event("b","p0"))
    return s.data


def controls():
    return [
        six("six_mode_five_certainties","1","0"),
        six("six_mode_ordinary_scattering","1/9","0"),
        six("six_mode_conditioned_transfers","1","0",conditioned=True),
        six("six_mode_memory_no_transfer","1","0",free=True),
        six("six_mode_transfer_tolerance_edge","1","4/5"),
        six("six_mode_transfer_tolerance_below","1","79/100"),
        six("six_mode_common_one_fifth_floor","1/5","0"),
        five("five_mode_shared_pair_residues","1/4","1/4","1/2"),
        five("five_mode_shared_pair_born","1/4","1/36","1/18"),
        five("five_mode_unmatched_refinements","1/4","1/4","1/2",omit_shared=True),
    ]


if __name__ == "__main__":
    import json
    print(json.dumps(controls(),separators=(",",":")))
