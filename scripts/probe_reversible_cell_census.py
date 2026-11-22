"""Infer a local cell rule from timing, not from a prespecified swap or conserved bit.

A petal of n equal logical hops has n-1 indistinguishable binary memory
cells. At a cell the inputs are an ingress side, a carried bit and the stored
bit. Outputs are an egress side, an outgoing bit and a new stored bit. Require
only the SAME reciprocal local map everywhere: it is an involution on all 8
states. Thus reflection, bit creation/loss and intrinsic handedness are all
initially permitted. Blank initial cells, a marked launch, and a hub that
continues unmarked circuits and signals on the next marked return are supplied.
The squared passage time is a synthetic training requirement, NOT lab data.

All 764 labelled maps are retained, not only the winners. The preselected
training lengths are 2,3 forward; holdouts are 4..12 in both directions and
the reversed training preparations. All lower-time failures and failures to
return by the specified deadline are restricted to the stated contract.
"""

from __future__ import annotations

import argparse
import json
from collections import Counter
from itertools import product
from pathlib import Path

from scripts.probe_bipartite_triangle_origin import need
from scripts.probe_reversible_excitation_detector import Apparatus


def involutions(k):
    table = [-1]*k

    def gen():
        if -1 not in table:
            yield tuple(table)
            return
        a = table.index(-1)
        for b in range(a,k):
            if table[b] == -1:
                table[a],table[b] = b,a
                yield from gen()
                table[a] = table[b] = -1
    yield from gen()


def shift(mask, bit, value):
    return (mask | bit) if value else (mask & ~bit)


def passage(rule, n, direction=1, mask=0, *, budget=None):
    """Exact logical hops; distinct hub ports 0 and n meet the same hub."""
    x, d, b = (0 if direction == 1 else n), direction, 1
    returns = []
    for t in range(1,1+(n*n if budget is None else budget)):
        x += d
        if x in (0,n):
            returns.append((t,d,b))
            if b:
                return (t,d,mask),tuple(returns)
            x = 0 if d == 1 else n
        else:
            bit = 1 << (x-1)
            raw = 4*int(d == -1) + 2*b + int(bool(mask & bit))
            out = rule[raw]
            d = 1 if out & 4 else -1
            b = (out//2) % 2
            mask = shift(mask,bit,out & 1)
    return None,tuple(returns)


class TablePetal(Apparatus):
    """Independent physical replay with four reciprocal edge hops per logical step."""

    def __init__(self, sizes, rule):
        self.rule = rule
        super().__init__(sizes)

    def scatter(self, v, ingress, mask):
        if v not in self.cells:
            return super().scatter(v,ingress,mask)
        bit,ports,names = self.cells[v]
        side,b = names[ingress]
        z = self.rule[4*int(side == 1)+2*b+int(bool(mask & bit))]
        return ports[(1 if z & 4 else -1),(z//2) % 2],shift(mask,bit,z & 1)


def hardware_passage(rule, n, d, mask):
    g = TablePetal((n,),rule)
    s = g.launch(0,d,mask)
    contacts = []
    for t in range(1,4*n*n+1):
        if s[1] == 0:
            lane = g.arc[s[:2]][1]
            direction = next(dd for dd in (-1,1) if s[0] == g.starts[0,-dd,lane])
            need(t % 4 == 0, "fractional logical hop in physical mesh")
            contacts.append((t//4,direction,lane))
            if lane:
                return (t//4,direction,s[2]),tuple(contacts)
        s = g.step(s)
    return None,tuple(contacts)


def fit(rule, cases):
    time_ok = state_ok = True
    for n,d in cases:
        got,_ = passage(rule,n,d)
        time_ok &= got is not None and got[0] == n*n
        state_ok &= got == (n*n,d,0)
    return time_ok,state_ok


def inferred_rule(reverse_transfer, reverse_double):
    result = []
    for side,b,m in product((0,1), repeat=3):
        reflect = reverse_transfer if b != m else bool(b and reverse_double)
        result.append(4*(side if reflect else 1-side)+2*m+b)
    return tuple(result)


def lift_stateless(s):
    # Second side/bit system, now with no cell at all. Add an untouched
    # spectator bit just to reuse the same independently checked evaluator.
    return tuple(2*s[z//2]+(z % 2) for z in range(8))


def encode(table):
    return "".join(map(str,table))


def census():
    train = ((2,1),(3,1))
    held = ((2,-1),(3,-1),*product(range(4,13),(-1,1)))
    entries = []
    for table in involutions(8):
        training = fit(table,train)
        holdout = fit(table,held)
        # flags in order: training time, training reset+direction+time,
        # holdout time, holdout reset+direction+time. Evaluate ALL holdouts,
        # including for candidates the training requirements did not favor.
        bits = "".join("1" if x else "0" for x in (*training,*holdout))
        entries.append((encode(table),bits))
    no_memory = []
    for table in involutions(4):
        rule = lift_stateless(table)
        flags = (*fit(rule,train),*fit(rule,held))
        no_memory.append((encode(table),"".join("1" if x else "0" for x in flags)))
    return sorted(entries),sorted(no_memory)


def controls(entries):
    training = {q for q,flags in entries if flags[0] == "1"}
    surviving = {q for q,flags in entries if flags == "1111"}
    choices = {(x,y):inferred_rule(x,y) for x,y in product((False,True),repeat=2)}
    need(len(entries) == 764 and len({q for q,_ in entries}) == 764 and
         len(training) == 6 and surviving == set(map(encode,choices.values())),
         "complete four-route census changed")
    need({q for q,flags in entries if flags[0] == flags[2] == "1"} == surviving,
         "timing-only holdout changed")
    for key,table in choices.items():
        transfer,double = key
        need(all((table[i]&3).bit_count() == (i&3).bit_count() and
                 table[i^4] == (table[i]^4) for i in range(8)),
             "surviving table need not conserve marks or respect reversal")
        for n,d in product(range(1,9),(-1,1)):
            got,visits = passage(table,n,d)
            need(got == (n*n,d,0) and len(visits) == n, "blank passage train")
            for mask in (0,(1 << (n-1))-1,1 if n > 1 else 0):
                need(passage(table,n,d,mask) == hardware_passage(table,n,d,mask),
                     "logical and physical calendars disagree")
        # Two hub-local observations distinguish all four, without reading the
        # hidden cell contents *after* the experiment. The second probe does
        # require preparing two stored marks in addition to the launched mark.
        _,blank = passage(table,5)
        full,_ = passage(table,3,mask=3)
        need(blank[0] == ((2,-1,0) if transfer else (5,1,0)) and full is not None and
             full[0] == (2 if double else 3), "two-preparation signature")
    # Independently check the simpler no-memory search and the two near misses
    # using the physical two-lane apparatus on both selected short lengths.
    for s in involutions(4):
        need(not fit(lift_stateless(s),((2,1),(3,1)))[0], "stateless winner")
    near = []
    for q in sorted(training-surviving):
        rule = tuple(map(int,q))
        for n in (2,3,4):
            need(hardware_passage(rule,n,1,0) == passage(rule,n), "near miss hardware")
        failed = next((n,d) for n,d in (*product((2,3),(-1,)),*product(range(4,13),(-1,1)))
                      if not fit(rule,((n,d),))[0])
        near.append((q,failed))
    return sorted(surviving),near


def registry(entries, stateless):
    return {"schema":"idt-reciprocal-cell-census/1",
            "word_code":"lexical outputs in input order: side, carried bit, stored bit",
            "flags":"train times; train times with reset and direction; holdout times; holdout with both",
            "train":"forward blank n=2,3", "holdout":"reverse blank n=2,3 and both directions n=4..12",
            "two_bit_tables":[list(r) for r in entries],
            "stateless_side_lane_tables":[list(r) for r in stateless]}


def main(argv=None):
    p = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    p.add_argument("--emit-census",action="store_true",help="emit every evaluated labelled table, including near misses")
    args = p.parse_args(argv)
    rows,smaller = census()
    entire = registry(rows,smaller)
    if args.emit_census:
        print(json.dumps(entire,separators=(",",":")))
        return
    survivors,near = controls(rows)
    path = Path(__file__).resolve().parents[1]/"data"/"reciprocal_cell_census.json"
    need(json.loads(path.read_text(encoding="utf-8")) == entire, "pinned complete census changed")
    print(f"{len(smaller)} stateless rules; {len(rows)} one-cell-bit involutions. "
          f"Training timing alone: 6, full training and holdout: {survivors}; timing near misses: {near}. "
          f"Flag census: {dict(sorted(Counter(flags for _,flags in rows).items()))}. "
          "Blank dwell times do not identify passage versus reflection on transfer or double mark.")


if __name__ == "__main__":
    main()
