"""Finite scheduled compiler for the active ternary fixture, using only bits.

E has no control port: it flips 000 <-> 111, leaving every mixed triple fixed.
Its offers still require supplied addresses and order. Little-endian pair
codes are T=00 (a hole), a=10, b=01 in site order, not integer display order.
This is not the two-input reversible binary law studied in the pair wall.
Run: python3 -m scripts.probe_binary_unanimous_triples [--json].
"""

import argparse
import json
from collections import Counter
from functools import lru_cache
from itertools import combinations, permutations, product

from scripts import probe_ternary_active_readout as cs
from scripts import probe_ternary_vacancy_switch as vac
from scripts.probe_eight_label_interferometer import check


CODE = {"T": 0, "a": 1, "b": 2}
CS = ((0, 2, 4), (1, 3, 4), (0, 2, 4), (0, 1, 3), (1, 2, 3), (0, 1, 3))
CS_LOW = ((0, 1, 2), (1, 2, 3), (0, 1, 3), (2, 3, 4), (1, 2, 3),
          (0, 1, 2), (1, 3, 4), (0, 2, 4), (1, 3, 4))
FREDKIN = ((0, 1, 3), (0, 2, 3), (0, 1, 3))


def offer(state, mask):
    part = state & mask
    return state ^ mask if part == 0 or part == mask else state


def masks(word):
    return tuple(sum(1 << i for i in triple) for triple in word)


def trace(start, word):
    history = [start]
    for mask in masks(word):
        history.append(offer(history[-1], mask))
    return tuple(history)


def equivariant_tables():
    """All 8! bijections, filtered by the two generators of site permutations."""
    swaps = [tuple(sum(((s >> j) & 1) << i for i, j in enumerate(order))
                   for s in range(8)) for order in ((1, 0, 2), (0, 2, 1))]
    return tuple(t for t in permutations(range(8))
                 if all(t[p[s]] == p[t[s]] for p in swaps for s in range(8)))


def image_ball(start, depth):
    """Simultaneous action on ordered input rows, all ten unordered triples."""
    maps = [tuple(offer(s, m) for s in range(32))
            for m in masks(combinations(range(5), 3))]
    seen = front = {tuple(start)}
    for _ in range(depth):
        front = {tuple(table[s] for s in row) for table in maps for row in front} - seen
        seen = seen | front
    return seen


def helper_free_obstructions():
    """All injective common ordered two-bit codes (a,b,T), no other site.

    aa -> bb forces 2*w(a) == 2*w(b) mod 3, hence w(a)=w(b) in [0,2].
    Distinct codes of equal weight must both weigh one. With two ones on
    four sites every triple is mixed: even the first move is impossible.
    """
    reasons = Counter()
    for a, b, _ in permutations(range(4), 3):
        start, end = a | a << 2, b | b << 2
        if start.bit_count() % 3 != end.bit_count() % 3:
            reasons["residue"] += 1
        else:
            check(start != end and all(offer(start, m) == start and offer(end, m) == end
                                       for m in masks(combinations(range(4), 3))), "not jammed")
            reasons["jammed"] += 1
    return dict(reasons)


def local_audit():
    tables = equivariant_tables()
    expected = {tuple(x ^ (7 if (u if x in (0, 7) else m) else 0) for x in range(8))
                for u, m in product(range(2), repeat=2)}
    check(set(tables) == expected, "role-free reversible classification")
    starts, goals = [], []
    leakage = wrong = 0
    for x, y in product("abT", repeat=2):
        u, v = cs.contact(x, y)
        start, goal = 16 | CODE[x] | CODE[y] << 2, 16 | CODE[u] | CODE[v] << 2
        history = trace(start, CS)
        check(history[-1] == goal, "CS truth table or helper restoration")
        check(trace(start ^ 16, CS_LOW)[-1] == (goal ^ 16), "CS low helper alternative")
        leakage += any((s & 3) == 3 or ((s >> 2) & 3) == 3 for s in history[1:-1])
        wrong += trace(start ^ 16, CS)[-1] != (goal ^ 16)
        starts.append(start)
        goals.append(goal)
    # Any witness of length <= 5 splits as <= 3 forward and <= 2 backward.
    check(not (image_ball(starts, 3) & image_ball(goals, 2)), "shorter CS compiler")
    check(not (image_ball([s ^ 16 for s in starts], 4) &
               image_ball([s ^ 16 for s in goals], 4)), "shorter low-helper CS compiler")
    for s in range(32):
        history = trace(s, CS)
        check(trace(s ^ 31, CS) == tuple(v ^ 31 for v in history), "global complement")
        check(trace(history[-1], CS[::-1]) == history[::-1], "off-code inverse")
        check(all(v.bit_count() % 3 == s.bit_count() % 3 for v in history), "raw residue")
    for c, a, b in product(range(2), repeat=3):
        start = 8 | c | a << 1 | b << 2
        goal = (8 | c | b << 1 | a << 2) if c else start
        check(trace(start, FREDKIN)[-1] == goal, "clean-bit Fredkin")
    return {"equivariant_tables": tables, "cs_rows": len(starts), "fredkin_rows": 8,
            "min_offers_fixed_code_high_bit": len(CS), "min_offers_fixed_code_low_bit": len(CS_LOW),
            "no_helper_codes": helper_free_obstructions(),
            "raw_inverse_complement_rows": 32, "transient_invalid_pair_rows": leakage,
            "wrong_clean_bit_failures": wrong}


@lru_cache(maxsize=None)
def addressed(i, j, h):
    slots = (2*i, 2*i+1, 2*j, 2*j+1, h)
    return masks(tuple(tuple(slots[k] for k in t) for t in CS))


def launch(raw, word, ports, checkpoints=None):
    """Carry the same bit state through every offer. Oracles only assert."""
    cat = len(raw)
    ref = [*(cs.RECODE[x] for x in raw), "a", *(("b", "b") * len(ports))]
    h = 2 * len(ref)
    state = (1 << h) | sum(CODE[x] << (2*i) for i, x in enumerate(ref))

    def cell(i):
        return (state >> (2*i)) & 3

    def contact(i, j):
        nonlocal state
        for mask in addressed(i, j, h):
            state = offer(state, mask)
        cs.step(ref, (i, j))
        # No other bit was addressed, so these checks induct to the full word.
        check(cell(i) == CODE[ref[i]] and cell(j) == CODE[ref[j]] and state >> h == 1,
              "binary state diverged from native CS at a six-offer cut")

    route_ref = list(raw)
    for n, (i, j) in enumerate(word, start=1):
        for e in cs.mapped(cs.VACANCY, (i, j, cat)):
            contact(*e)
        route_ref[i], route_ref[j] = vac.contact(route_ref[i], route_ref[j])
        check(cell(cat) == CODE["a"] and all(cell(k) == CODE[cs.RECODE[x]]
                                             for k, x in enumerate(route_ref)), "vacancy cut")
        if checkpoints and n in checkpoints:
            check(all(cell(k) == CODE[x] for k, x in enumerate(checkpoints[n])), "hub cut")
    held_mask = (1 << (2 * (cat + 1))) - 1
    held = state & held_mask
    for k, p in enumerate(ports):
        r = cat + 1 + 2*k
        for e in cs.mapped(cs.PROTECTED_METER, (p, r, r+1, cat)):
            contact(*e)
            check(cell(r) in (1, 2) and cell(r+1) in (1, 2), "logical record protection")
        check(state & held_mask == held, "meter disturbed held data or ternary catalyst")
    records = tuple((cell(r), cell(r+1)) for r in range(cat+1, len(ref), 2))
    check(all(p in ((1, 1), (2, 2)) for p in records), "invalid ordinary record")
    return tuple(int(a == 1) for a, _ in records)


def resources(word_lengths, data, ports):
    return {"bits": 2*(data + 1 + 2*ports) + 1,
            "data_pairs": data, "restored_a_pairs": 1, "ordinary_record_pairs": 2*ports,
            "shared_clean_high_bits": 1,
            "max_offers": len(CS)*(max(word_lengths)*len(cs.VACANCY) + ports*len(cs.PROTECTED_METER))}


def apparatus_audit():
    rows, lengths = [], []
    launches = vacuum = 0
    for source, plates, opened in product(range(2), vac.BITS, vac.BITS):
        counts = [0]*3
        for seeds, fills in product(vac.BITS, repeat=2):
            tr = vac.trial(source, plates, opened, seeds, fills)
            marks = launch(tr.states[0], tr.word, cs.PORTS)
            obs = (*marks[:2], sum(marks[2:]))
            check(marks == tuple(int(tr.states[-1][i] == "T") for i in cs.PORTS)
                  and obs == tr.outcome, "two-arm records")
            counts = [a+b for a, b in zip(counts, obs, strict=True)]
            launches += 1
            for replacement in ("V", "N"):
                empty = tuple(replacement if x == "T" else x for x in tr.states[0])
                check(not any(launch(empty, tr.word, cs.PORTS)), "false vacuum record")
                vacuum += 1
        lengths.append(len(tr.word))
        check(tuple(counts) == vac.frozen.mobile._expected(source, plates, opened), "two-arm counts")
        rows.append((source, plates, opened, tuple(counts)))
    two = {"rows": rows, "launches": launches, "vacuum_controls": vacuum,
           **resources(lengths, 2*vac.STRIDE, len(cs.PORTS))}
    matrices, lengths = {}, []
    launches = hubs = 0
    f = vac.frozen
    for name, edges in (("chain", f.CHAIN), ("triangle", f.TRIANGLE), ("repeated", f.REPEATED)):
        blocks = [vac.switch(a, b, 3) for a, b in edges]
        word = tuple(e for block in blocks for e in block)
        lengths.append(len(word))
        matrix = []
        for source in range(3):
            counts = [0]*3
            for bits in product(range(2), repeat=3):
                raw = tuple(x for i in range(3) for x in
                            ("T" if i == source else "N", *vac.stock(bits[i])))
                ref = [(3 if i == source else 1, 1+bits[i]) for i in range(3)]
                cuts = {}
                n = 0
                for (a, b), block in zip(edges, blocks, strict=True):
                    ref[a], ref[b] = f.device((ref[a], ref[b]), "U")
                    n += len(block)
                    cuts[n] = tuple(cs.RECODE[x] for d, e in ref for x in
                                    ("T" if d == 3 else "N", *vac.stock(e-1)))
                marks = launch(raw, word, (0, 3, 6), cuts)
                check(marks == tuple(int(d == 3) for d, _ in ref), "three-port records")
                counts = [a+b for a, b in zip(counts, marks, strict=True)]
                launches += 1
                hubs += len(cuts)
            matrix.append(counts)
        matrices[name] = matrix
    return {"two_arm": two, "three_port": {"launches": launches, "hub_checks": hubs,
            "counts_over_eight": matrices, **resources(lengths, 9, 3)}}


def verify():
    return {"scope": "Finite scheduled compiler from addressed binary three-site offers.",
            "local": local_audit(), **apparatus_audit(),
            "offers_per_active_contact": len(CS),
            "offers_per_vacancy_contact": len(CS)*len(cs.VACANCY),
            "offers_per_protected_meter": len(CS)*len(cs.PROTECTED_METER),
            "boundary": "The pair code, shared initialized high bit, ternary stocks, addressed "
                        "triples and timing are supplied. Hole count and record protection refer "
                        "to logical cuts, not every raw offer: raw weight can change by three. "
                        "Not a self-assembled detector, capture, queue, clock, or physical law. "
                        "Six is minimal only for this exact code, clean high helper, full nine-row "
                        "target and freely addressed five-bit words; not a global hardware optimum."}


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--json", action="store_true")
    args = parser.parse_args()
    report = verify()
    if args.json:
        print(json.dumps(report, indent=2))
    else:
        print(report["scope"])
        print("offers / CS, vacancy, meter:", report["offers_per_active_contact"],
              report["offers_per_vacancy_contact"], report["offers_per_protected_meter"])
        print("two-arm launches / vacuum controls:", report["two_arm"]["launches"],
              report["two_arm"]["vacuum_controls"])
        print("three-port launches / cuts:", report["three_port"]["launches"],
              report["three_port"]["hub_checks"])
        print(report["boundary"])
