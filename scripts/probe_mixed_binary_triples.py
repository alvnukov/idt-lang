"""Finite mixed-triple comparator to the unanimous binary contact E.

The address has three unordered sites. M fixes monochrome triples and flips
all three sites on mixed triples: it uses internal equality, no control port.
Ordered *offers* and a two-bit home for each symbol are external apparatus.
Run: python3 -m scripts.probe_mixed_binary_triples [--json].
"""

import argparse
import json
from functools import lru_cache
from itertools import combinations, product

from scripts import probe_binary_unanimous_triples as e
from scripts import probe_ternary_active_readout as cs
from scripts import probe_ternary_vacancy_switch as vac
from scripts.probe_eight_label_interferometer import check


A, B, C, D = combinations(range(4), 3)  # 012, 013, 023, 123
CS4 = (A, B, D, A, B, D, A, D, B, C, B, C, A)
CS5 = ((0, 2, 4), D, (1, 3, 4), B, D, (1, 3, 4), B, (0, 2, 4))
CS5_LOW = (B, (2, 3, 4), D, (0, 2, 4), B, (0, 3, 4), C, (1, 3, 4), A, D, (2, 3, 4))


def offer(state, mask):
    return state if state & mask in (0, mask) else state ^ mask


def replay(state, word):
    for mask in e.masks(word):
        state = offer(state, mask)
    return state


def rows(helper):
    h = (helper or 0) << 4
    pairs = tuple(product(e.CODE, repeat=2))

    def encode(pair):
        x, y = pair
        return e.CODE[x] | e.CODE[y] << 2 | h

    return bytes(map(encode, pairs)), bytes(encode(cs.contact(*p)) for p in pairs)


def image_ball(start, tables, depth):
    # The nine rows move under ONE common address at each step.
    seen = front = {start}
    for _ in range(depth):
        front = {row.translate(t) for t in tables for row in front} - seen
        seen = seen | front
    return seen


def compiler_audit(helper, word):
    width = 4 + (helper is not None)
    start, goal = rows(helper)
    spare = 0
    for s, g in zip(start, goal, strict=True):
        history = [s]
        for mask in e.masks(word):
            history.append(offer(history[-1], mask))
        check(history[-1] == g, "wrong code or unrestored helper")
        spare += any((v & 3) == 3 or (v >> 2 & 3) == 3 for v in history[1:-1])
    # Test every unordered triple, not just those occurring in the witness.
    tables = [bytes(offer(s, m) for s in range(256))
              for m in e.masks(combinations(range(width), 3))]
    left = (len(word) - 1) // 2
    right = len(word) - 1 - left
    f, b = image_ball(start, tables, left), image_ball(goal, tables, right)
    check(f.isdisjoint(b), "a shorter word exists")
    return {"lower_bound": len(word), "witness": word, "raw_bits": width,
            "radii": [left, right], "ball_sizes": [len(f), len(b)],
            "clean_input_rows": len(start), "transient_spare_rows": spare}


def jammed_words(width, masks):
    return {s for s in range(1 << width) if all(offer(s, m) == s for m in masks)}


def components(size, edges):
    parents = list(range(size))

    def find(i):
        while parents[i] != i:
            parents[i] = i = parents[parents[i]]
        return i

    for i, j in edges:
        parents[find(i)] = find(j)
    return [find(i) for i in range(size)]


def support_audit(helper):
    """Reachability on clean CUTS via arbitrary finite paths, not next returns.

    Count unordered pairs of *distinct* code states: equality is automatically
    reachable by the empty word. This is not a positive-time fixed-row test.
    """
    width = 4 + (helper is not None)
    n = 1 << width
    triples = tuple(combinations(range(width), 3))
    masks = e.masks(triples)
    transitions = [[(s, t) for s in range(n) if s < (t := offer(s, m))] for m in masks]
    start, goal = rows(helper)
    native = {tuple(sorted((s, t))) for s, t in zip(start, goal, strict=True) if s != t}
    clean = list(combinations(sorted(start), 2))
    exact = all_reached = 0
    best = None
    for bits in range(1 << len(masks)):
        selected = [j for j in range(len(masks)) if bits >> j & 1]
        cc = components(n, (edge for j in selected for edge in transitions[j]))
        got = {(s, t) for s, t in clean if cc[s] == cc[t]}
        exact += got == native
        if native <= got:
            all_reached += 1
            extra = len(got - native)
            best = extra if best is None else min(extra, best)
        # Each offered triple must be monochrome to jam. Equality propagates
        # through each incidence component; isolated sites impose no condition.
        ids = components(width, (edge for j in selected for edge in combinations(triples[j], 2)))
        actual = jammed_words(width, [masks[j] for j in selected])
        predicted = {s for s in range(n) if all((s >> i ^ s >> k) & 1 == 0
                                               for i, k in enumerate(ids))}
        check(actual == predicted, "componentwise-constant jamming control")
    return {"supports": 1 << len(masks), "helper": helper, "exact_supports": exact,
            "native_distinct_pairs": len(native), "all_desired_reachable": all_reached,
            "minimum_extra_if_all_desired": best}


@lru_cache(maxsize=None)
def addressed(i, j):
    slots = (2*i, 2*i+1, 2*j, 2*j+1)
    return e.masks(tuple(tuple(slots[k] for k in triple) for triple in CS4))


def launch(raw, logical_word, ports):
    """Carry bits through every M offer, with no intervening decoding/reset."""
    cat = len(raw)
    inputs = tuple(cs.RECODE[x] for x in raw) + ("a",) + ("b", "b") * len(ports)
    state = sum(e.CODE[x] << (2*i) for i, x in enumerate(inputs))

    def run(word, sites):
        nonlocal state
        for i, j in cs.mapped(word, sites):
            for m in addressed(i, j):
                state = offer(state, m)

    for i, j in logical_word:
        run(cs.VACANCY, (i, j, cat))
    held_mask = (1 << (2*(cat+1))) - 1
    held = state & held_mask
    check((held >> (2*cat)) == e.CODE["a"], "unrestored vacancy catalyst")
    records = []
    for k, port in enumerate(ports):
        r = cat + 1 + 2*k
        run(cs.PROTECTED_METER, (port, r, r+1, cat))
        pair = state >> (2*r) & 15
        check((state & held_mask) == held and pair in (5, 10), "held data or record code")
        records.append(int(pair == 5))
    return tuple(records)


def apparatus_audit():
    launches = controls = three = 0
    for source, plates, opened in product(range(2), vac.BITS, vac.BITS):
        totals = [0]*3
        for seeds, fills in product(vac.BITS, repeat=2):
            tr = vac.trial(source, plates, opened, seeds, fills)
            marks = launch(tr.states[0], tr.word, cs.PORTS)
            check(marks == tuple(int(tr.states[-1][i] == "T") for i in cs.PORTS), "two-arm ports")
            observed = (*marks[:2], sum(marks[2:]))
            check(observed == tr.outcome, "two-arm transport")
            totals = [x+y for x, y in zip(totals, observed, strict=True)]
            launches += 1
            for replacement in "VN":
                empty = tuple(replacement if x == "T" else x for x in tr.states[0])
                check(not any(launch(empty, tr.word, cs.PORTS)), "ordinary-stock false mark")
                controls += 1
        check(tuple(totals) == vac.frozen.mobile._expected(source, plates, opened), "counts")
    matrices = {}
    for name, edges in (("chain", vac.frozen.CHAIN), ("triangle", vac.frozen.TRIANGLE),
                        ("repeated", vac.frozen.REPEATED)):
        word = tuple(e for i, j in edges for e in vac.switch(i, j, 3))
        matrix = []
        for source in range(3):
            counts = [0]*3
            for bits in product(range(2), repeat=3):
                raw = tuple(x for i in range(3) for x in
                            ("T" if i == source else "N", *vac.stock(bits[i])))
                ref = [(3 if i == source else 1, 1+bits[i]) for i in range(3)]
                for i, j in edges:
                    ref[i], ref[j] = vac.frozen.device((ref[i], ref[j]), "U")
                marks = launch(raw, word, (0, 3, 6))
                check(marks == tuple(int(d == 3) for d, _ in ref), "three-port detector")
                counts = [x+y for x, y in zip(counts, marks, strict=True)]
                three += 1
            matrix.append(counts)
        matrices[name] = matrix
    return {"two_arm_launches": launches, "ordinary_source_controls": controls,
            "three_port_launches": three, "three_port_counts_over_eight": matrices,
            "two_arm_data_bits_including_stocks_and_registers": 2*(2*vac.STRIDE+1+2*len(cs.PORTS)),
            "three_port_data_bits_including_stocks_and_registers": 2*(9+1+2*3),
            "offers_per_vacancy": len(CS4)*len(cs.VACANCY),
            "offers_per_protected_meter": len(CS4)*len(cs.PROTECTED_METER)}


def verify():
    table = tuple(offer(s, 7) for s in range(8))
    check(table in e.equivariant_tables() and all(table[table[s]] == s for s in range(8)),
          "not an anonymous involution")
    check(offer(1, 7) == 6 and e.offer(1, 7) == 1 and e.offer(0, 7) == 7,
          "raw vacuum and weight controls")
    return {"scope": "Finite scheduled binary-triple competitor; not an autonomous apparatus.",
            "local_table": table, "no_helper": compiler_audit(None, CS4),
            "high_helper": compiler_audit(1, CS5), "low_helper": compiler_audit(0, CS5_LOW),
            "apparatus_no_helper": apparatus_audit(),
            "unclocked_supports": [support_audit(h) for h in (None, 0, 1)],
            "boundary": "Code, home assignments, stocks, addresses, offer order and read cuts "
                        "are supplied. Raw all-zero is quiescent; an ordinary-source control "
                        "is an encoded prepared apparatus, not the all-zero word. Minima are "
                        "only for the stated encoding and initialized/restored helper budget. "
                        "The support comparison concerns distinct endpoint reachability, not "
                        "positive-time returns, rates or controllers. No physical selection."}


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--json", action="store_true")
    args = parser.parse_args()
    result = verify()
    if args.json:
        print(json.dumps(result, indent=2))
    else:
        print(result["scope"])
        for key in ("no_helper", "high_helper", "low_helper"):
            print(key, "minimum scheduled offers:", result[key]["lower_bound"])
        print("unscheduled support comparisons:", result["unclocked_supports"])
        print("no-helper transport:", result["apparatus_no_helper"])
        print(result["boundary"])
