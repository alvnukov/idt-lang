"""Fixed-frame comparison of an anchored collision with a translated rival.

The zero-record calibration was known when these alternatives were chosen.
There is no withheld physical observation. This is an out-of-calibration
design: the checked numerical predictions can be distinguished by one
physical tag count IF preparation, command, and readout are available.
"""

from collections import Counter
from itertools import permutations, product

from scripts.probe_blind_collision_charge import (
    LARGE,
    PORTS,
    SMALL,
    STATES,
    fire,
    hop,
    occ,
    relabel,
    ternary_library,
)


def need(test, why):
    if not test:
        raise ArithmeticError(why)


def shifted(triple):
    # Work with equality of packets, not with a privileged zero-record.
    for i, j, k in ((0, 1, 2), (0, 2, 1), (1, 2, 0)):
        if triple[i] == triple[j] and triple[i] != triple[k]:
            d = triple[i] ^ triple[k]
            large = [h for h in LARGE if d >> h & 1]
            small = [h for h in SMALL if d >> h & 1]
            if len(large) == len(small) == 1:
                return tuple(hop(v, large[0]) for v in triple)
    return triple


def ballot(triple):
    return sum(-2*c+3*w for c,w in map(occ,triple))


def probe():
    rule = ternary_library()[1][1, 1, "large", 1]
    active, relative, preserved = set(), set(), set()
    changes = Counter()
    all_triples = tuple(product(STATES, repeat=3))
    for t in all_triples:
        a, b = fire(t,rule), shifted(t)
        need(fire(a,rule) == shifted(b) == t, "not reversible")
        if t.count(0) >= 2 or t != a:
            need(a == b, "rivals differ on a calibration")
        if a != t:
            active.add(t)
        if b != t:
            relative.add(t)
            delta = ballot(b)-ballot(t)
            changes[delta] += 1
            if not delta:
                preserved.add(t)
        # Passive recoding of all three inputs leaves the relative command
        # covariant, unlike actively moving packets with the absolute anchor
        # held fixed. Exhaust all translations on the even records.
        for offset in STATES:
            need(shifted(tuple(x ^ offset for x in t)) == tuple(x ^ offset for x in b), "absolute root leaked")
    for p,q in product(permutations(LARGE),permutations(SMALL)):
        mapping = p+q
        for t in relative:
            need(shifted(tuple(relabel(x,mapping) for x in t)) == tuple(relabel(x,mapping) for x in shifted(t)),
                 "port relabeling changed law")
    need(len(PORTS) == 5 and len(all_triples) == 4096 and (len(active),len(relative)) == (36,288), "domain count")
    need(preserved == active and active < relative and sum(changes.values()) == len(relative), "restriction not maximal")
    need(changes == {0:36, 6:54, -6:54, 12:36, -12:36, 18:18, -18:18, 24:18, -24:18}, "delta census")
    original, translated = (0,0,9), (24,24,17)
    common = fire(original,rule)
    need(common == shifted(original) == (30,30,23), "calibrated command")
    need(fire(translated,rule) == translated and shifted(translated) == (6,6,15), "fixed-mark comparison")
    need((ballot(translated),ballot(shifted(translated))) == (13,-11), "optional downstream check")
    return {"calibrated":common, "same_preparation":translated, "anchored_mark_count":2, "relative_mark_count":0,
            "translated":shifted(translated), "ordered_active":[len(active),len(relative)],
            "nonmatching_active": len(relative-active), "signed_changes_on_relative_domain": dict(sorted(changes.items())),
            "experimental_status":"paired predictions only; no physical input or outcome"}


if __name__ == "__main__":
    import json
    print(json.dumps(probe(), sort_keys=True))
