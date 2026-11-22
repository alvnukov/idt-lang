"""Can a local port distinguish two cold-splitting laws starting with units only?

Two supplied synchronized, reciprocal circuits, fixed before comparing laws.
Stocks start at zero. Each initially occupied directed edge carries exactly one
unit. A cold storage node C, with ONE arriving packet k, transmits it over the
opposite port and updates k,s by E19 exchange or extremes_only. Both are
conservative involutions. With two packets arriving together, keep both on
their original ports and leave stock unchanged (a separately supplied reversible
extension); the two successful traces never use this convention. Relay ports
transmit in either direction; a terminal reflects. Opposite packets may pass
on one wire. Propagation uses one tick per edge. Full integer loads below
audit the model; the reported bit is only OCCUPIED on one outgoing B edge
at a prescribed tick, for all trials, without a load- or success-conditioned
gate. This is passive observation, not an internally constructed recorder.

Five-unit test: B is a ternary 110<->002 cell, A a quaternary 1110<->0003
cell. Fire the two and three source arms respectively. C is one hop from B
and four from A. B's pair arrives first, parks one unit and sends one onward.
A's later triple meets this stock, so k'=2 (exchange) or k'=3 (extremes).
Back at B an isolated pair splits; an isolated triple returns on its incoming
arm for ANY deterministic, conserving, anonymous three-port bijection on
that sector. Its input stabilizer interchanges the two empty arms; the only
fixed outputs at total 3 are that triple and (1,1,1), whose stabilizer is
larger. Equivariance of the inverse forbids the latter. The supplied circuit
uses identity outside the calibrated sectors.

Four-unit test: same B and C, now one hop from A. A additionally implements
the independent anonymous total-two calibration 1100<->0011. The singleton
from C and a third unit arrive together at A on two arms; the opposite two
receive singletons. Two one-edge terminal mirrors return them together with
the fourth unit on the third arm. A then sends a triple back to C. This
attains the mass lower bound: below four core units the two storage rules
coincide on EVERY possible nonempty incident load/stock pair. It does not
prove necessity of the extra calibration (or minimal wiring, time or arity).
Neither the mergers, their common timing, terminal preparations, named
observed link, nor any law of nature is inferred from the two-unit data.

Run: python3 -B -m scripts.probe_calibrated_unit_pile_comparator (also with -O).
"""

import json
from collections import Counter
from itertools import permutations

from scripts.probe_anonymous_port_fusion import compositions, local, permute
from scripts.probe_indistinguishable_mobile_load import exchange, extremes_only


def need(test, why):
    if not test:
        raise ArithmeticError(why)


def scatter(v, loads, s, law, pair_shell, enable_a, enable_b):
    if v == "C":
        x, y = loads
        if bool(x) == bool(y):
            return loads, s
        k, s = law(x or y, s)
        return ((0, k) if x else (k, 0)), s
    if v == "A" and enable_a:
        if pair_shell and sum(loads) == 2:
            return local(4, 2, loads), s
        return local(4, 3, loads), s
    if v == "B" and enable_b:
        return local(3, 2, loads), s
    if len(loads) == 2:  # ordinary through relay, two opposite inputs allowed
        return loads[::-1], s
    return loads, s  # reflecting terminal or explicit identity-gate control


def wiring(which, equal_paths=False):
    g = {}

    def edge(u, v):
        need(u != v and v not in g.get(u, ()), "repeated or loop wire")
        g.setdefault(u, []).append(v)
        g.setdefault(v, []).append(u)

    def path(u, v, length, name):
        seq = [u] + [name+str(i) for i in range(1, length)] + [v]
        for a, b in zip(seq, seq[1:]):
            edge(a, b)
        return seq

    # Terminal paths are physical, not fresh injections at prescribed later times.
    edge("B", "C")
    path("C", "A", 4 if which == 5 and not equal_paths else 1, "ca")
    arms = {}
    for h, n in (("A", 3), ("B", 2)):
        for i in range(n):
            name = f"{h}{i}"
            length = 1 if which == 4 and h == "A" and i > 0 else 8
            arms[name] = path(h, name+"end", length, name+"r")
    need(len(g["A"]) == 4 and len(g["B"]) == 3 and len(g["C"]) == 2
         and all(len(n) in (1, 2) for v, n in g.items() if v not in ("A","B","C")),
         "wrong port wiring")
    return g, arms


def preparation(which, arms, delayed=False):
    def unit(name, arrival):
        seq = arms[name]
        return seq[arrival+1], seq[arrival]

    source = [unit("B0", 0), unit("B1", int(delayed))]
    if which == 5:
        source += [unit("A"+str(i), 0) for i in range(3)]
    else:
        source += [unit("A0", 2), unit("A0", 4)]
    need(len(set(source)) == which, "a hidden initial pile")
    return Counter(source), 0


def step(g, arcs, stock, settings):
    result, next_stock, c_loads = Counter(), stock, ()
    for v, ports in g.items():
        incoming = tuple(arcs[p, v] for p in ports)
        outgoing, s = scatter(v, incoming, stock if v == "C" else 0, *settings)
        if v == "C":
            next_stock, c_loads = s, incoming
        for p, k in zip(ports, outgoing):
            if k:
                result[v, p] = k
    need(sum(arcs.values())+stock == sum(result.values())+next_stock, "mass violation")
    return result, next_stock, c_loads


def reverse(arcs):
    return Counter({(v,u): k for (u,v),k in arcs.items()})


def run(which, law, *, pair_shell=None, delayed=False, equal_paths=False,
        enable_a=True, enable_b=True):
    g, arms = wiring(which, equal_paths)
    arcs, stock = preparation(which, arms, delayed)
    settings = law, which == 4 if pair_shell is None else pair_shell, enable_a, enable_b
    read_tick = 5 if which == 5 else 6
    events, coarrivals, wire_crossings = [], [], []
    final_b_input = []
    for t in range(read_tick+1):
        out, new_stock, loads = step(g, arcs, stock, settings)
        inv, old_stock, _ = step(g, reverse(out), new_stock, settings)
        need(reverse(inv) == arcs and old_stock == stock, "wrong reverse trace")
        if any(loads):
            events.append([t, list(loads), stock, new_stock])
        if all(loads):
            coarrivals.append(t)
        if any(out[v,u] for u,v in out):
            wire_crossings.append(t)
        if sum(arcs[p,"B"] for p in g["B"]) and t == read_tick:
            final_b_input = [arcs[p,"B"] for p in g["B"]]
        arcs, stock = out, new_stock
    return {"observed_side_link_occupied": bool(arcs["B",arms["B0"][1]]),
            "read_scatter_tick_zero_based": read_tick, "audit_C_tick_ports_before_after_stock": events,
            "audit_C_concurrent_ticks": coarrivals, "audit_opposite_wire_ticks": wire_crossings,
            "audit_B_incoming_at_read": final_b_input}


def audit():
    n = 0
    for total in range(6):
        for x,y,s in compositions(total, 3):
            for law in (exchange, extremes_only):
                out, after = scatter("C",(x,y),s,law,False,True,True)
                need(scatter("C",out,after,law,False,True,True) == ((x,y),s) and
                     sum(out)+after == total, "nonreversible storage closure")
                if total < 4:
                    need(scatter("C",(x,y),s,exchange,False,True,True) ==
                         scatter("C",(x,y),s,extremes_only,False,True,True), "mass lower bound")
                n += 1
        for v,m,extra in (("B",3,False),("A",4,False),("A",4,True)):
            for w in compositions(total,m):
                def f(z):
                    return scatter(v,z,0,exchange,extra,True,True)[0]
                need(sum(f(w)) == total and f(f(w)) == w and
                     all(f(permute(w,p)) == permute(f(w),p) for p in permutations(range(m))),
                     "nonanonymous or nonreversible supplied gate")
    w = (3,0,0)
    sym = tuple(permutations(range(3)))
    stabilizer = lambda v: {p for p in sym if permute(v,p) == v}
    need([v for v in compositions(3,3) if stabilizer(v) == stabilizer(w)] == [w],
         "ternary triple could have another stabilizer-equivalent exit")
    return n


def probe():
    def contrast(which, **options):
        return [run(which, law, **options) for law in (exchange, extremes_only)]

    def bits(rows):
        return [r["observed_side_link_occupied"] for r in rows]

    checked = audit()
    five, four = contrast(5), contrast(4)
    for rows, first, mixed in ((five,1,4),(four,1,5)):
        need(bits(rows) == [True,False] and all(not r["audit_C_concurrent_ticks"] for r in rows),
             "lost one-bit distinction or used concurrent storage")
        for idx, r in enumerate(rows):
            need(r["audit_C_tick_ports_before_after_stock"] ==
                 [[first,[2,0],0,1],[mixed,[0,3],1,2-idx]] and
                 r["audit_B_incoming_at_read"] == [2+idx,0,0], "wrong preparation or read")
    need(all(2 in r["audit_opposite_wire_ticks"] for r in five), "missing five-unit wire crossing")
    controls = {}
    for label, which, opts in (("four_missing_pair_shell",4,{"pair_shell":False}),
                               ("four_delayed_B_arm",4,{"delayed":True}),
                               ("five_identity_A",5,{"enable_a":False}),
                               ("five_identity_B",5,{"enable_b":False}),
                               ("five_simultaneous_at_C",5,{"equal_paths":True})):
        rows = contrast(which, **opts)
        need(bits(rows)[0] == bits(rows)[1], "unexpected control distinction: "+label)
        if label == "five_simultaneous_at_C":
            need(all(1 in r["audit_C_concurrent_ticks"] for r in rows), "control missed coarrival")
        controls[label] = bits(rows)
    return {"scope":"finite static calibrated hardware; a timed passive binary port, not empirical",
            "law_order":["exchange","extremes_only"], "five_units_original_calibrations":five,
            "four_units_additional_A_total_two_calibration":four,
            "control_observed_bits":controls,"storage_involution_rows_including_both_laws":checked,
            "mixed_law_minimum_units":4,"four_without_extra_calibration":"not decided in general"}


if __name__ == "__main__":
    print(json.dumps(probe(),separators=(",",":")))
