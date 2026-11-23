"""A fixed ternary contact compiling vacancy routing AND writing ordinary records.

Run as python3 -m scripts.probe_ternary_active_readout [--json].
Finite scheduled fixture. The rule, graph, timing and initialized stocks are
supplied; no autonomous detector, physical probability law or theory upgrade.
"""

import argparse
import json
from collections import Counter, deque
from itertools import combinations, permutations, product

from scripts import probe_ternary_vacancy_switch as vacancy
from scripts.probe_eight_label_interferometer import check

FLIP = {"a": "b", "b": "a"}
RECODE = {"V": "a", "N": "b", "T": "T"}
A, B, C = ((0, 1), (0, 2), (1, 2))
VACANCY = (B, A, B, C, A, C, B, A, B)
METER = (C, A, C, B, A, C, B)
# Slots: private input, two ordinary records, shared restored a catalyst.
PROTECTED_METER = ((0, 3), (0, 1), (0, 3), (2, 3), (1, 2))
PORTS = (vacancy.D, vacancy.STRIDE + vacancy.D, vacancy.DUMP, vacancy.STRIDE + vacancy.DUMP)


def contact(x, y):
    if "T" not in (x, y):
        return FLIP[y], FLIP[x]
    return (y, x) if "a" in (x, y) else (x, y)


def step(state, edge):
    i, j = edge
    state[i], state[j] = contact(state[i], state[j])


def replay(raw, word):
    state = list(raw)
    history = [tuple(state)]
    for edge in word:
        step(state, edge)
        history.append(tuple(state))
    return tuple(history)


def sector_tables(pairs):
    for outputs in permutations(pairs):
        table = dict(zip(pairs, outputs, strict=True))
        if all(table[y, x] == table[x, y][::-1] and table[table[x, y]] == (x, y)
               for x, y in pairs):
            yield table


def classify():
    """Enumerate by preserved T-count; name sectors only AFTER the filters."""
    pairs = tuple(product("abT", repeat=2))
    zero = tuple(p for p in pairs if p.count("T") == 0)
    one = tuple(p for p in pairs if p.count("T") == 1)
    result = []
    for blank, mixed in product(sector_tables(zero), sector_tables(one)):
        # The four maps are distinguished by the images of aa and ab.
        reverses_ab = blank["a", "b"] == ("b", "a")
        if blank["a", "a"] == ("a", "a"):
            blank_name = "swap" if reverses_ab else "identity"
        else:
            blank_name = "complement" if reverses_ab else "complement-swap"
        moves = "".join(c for c in "ab" if mixed["T", c][1] == "T")
        if "b" in mixed["T", "a"]:
            mode = "exchange/move" if moves else "exchange/hold"
        else:
            mode = moves or "hold"
        table = blank | mixed | {("T", "T"): ("T", "T")}
        result.append((blank_name, mode, tuple(table[p] for p in pairs)))
    return tuple(result)


def audit_local():
    pairs = tuple(product("abT", repeat=2))
    tables = {(blank, mode): dict(zip(pairs, images, strict=True))
              for blank, mode, images in classify()}
    for x, y in pairs:
        out = contact(x, y)
        check(out == tables["complement-swap", "a"][x, y], "wrong native class")
        check(out.count("b") % 2 == (x, y).count("b") % 2, "b parity")
        goal = ((y, x) if "a" in (x, y) else (x, y)) + ("a",)
        check(replay((x, y, "a"), VACANCY)[-1] == goal, "full-alphabet compiler")
        # Bare identity-blank contacts keep the b sites fixed. Bare swap-blank
        # contacts merely transpose the a occupancy, as in the vacancy probe.
        identity = tables["identity", "a"][x, y]
        swap = tables["swap", "a"][x, y]
        check(tuple(z == "b" for z in identity) == (x == "b", y == "b"), "fixed b")
        check(tuple(z == "a" for z in swap) == (y == "a", x == "a"), "transposed a")

    compl = tables["complement", "a"]

    def complement_history(raw, word):
        state = list(raw)
        history = [tuple(state)]
        for i, j in word:
            state[i], state[j] = compl[state[i], state[j]]
            history.append(tuple(state))
        return history

    for x in "abT":
        goal = (x, "a", "a") if x == "T" else (x, "b", "b")
        for meter, suffix in ((METER, ()), (PROTECTED_METER, ("a",))):
            raw = (x, "b", "b") + suffix
            history = replay(raw, meter)
            check(history[-1] == goal + suffix and replay(history[-1], meter[::-1]) == history[::-1],
                  "ordinary marking, no-hit restoration or erasure")
            if suffix:
                check(all("T" not in st[1:3] for st in history), "protected meter exposure")
        # Complement, unlike complement-swap, can write with T strictly parked.
        history = complement_history((x, "b", "b"), (A, B, C))
        check(history[-1] == goal, "complement meter")
        if x == "T":
            check(all(st[0] == "T" for st in history), "complement meter moved T")
    for x, y, c in product("bT", "bT", "ab"):
        raw = (x, y, c)
        final = complement_history(raw, (A, B, C, A, C, B, A, B, C))[-1]
        check(final == ((y, x, c) if c == "b" else raw), "prepared complement controlled swap")
    return {"cs_vacancy_compiler_pairs": 9, "complement_stationary_detector_inputs": 3,
            "complement_prepared_controlled_swap_rows": 8,
            "boundary": "On blank-only inputs complement flips each contacted site's own shade, "
                        "so a fixed word cannot exchange two arbitrary unknown blanks. Its "
                        "prepared controlled swap is not a full vacancy compiler."}


def shortest_depth(start, goal, edges, protected=()):
    """BFS on simultaneous ordered test rows, rejecting even transient T exposure."""
    queue = deque([(start, 0)])
    seen = {start}
    while queue:
        rows, depth = queue.popleft()
        if rows == goal:
            return depth
        for edge in edges:
            nxt = tuple(replay(row, (edge,))[-1] for row in rows)
            if any(row[i] == "T" for row in nxt for i in protected):
                continue
            if nxt not in seen:
                seen.add(nxt)
                queue.append((nxt, depth + 1))
    return None


def triangle_depths():
    inputs = tuple((x, y, "a") for x, y in product("abT", repeat=2))
    goal = tuple(((y, x) if "a" in (x, y) else (x, y)) + ("a",) for x, y, _ in inputs)
    meters = tuple((x, "b", "b") for x in "abT")
    marked = (meters[0], meters[1], ("T", "a", "a"))
    edges = (A, B, C)
    return {"vacancy": shortest_depth(inputs, goal, edges),
            "meter": shortest_depth(meters, marked, edges)}


def protected_depth():
    inputs = tuple((x, "b", "b", "a") for x in "abT")
    goal = (*inputs[:2], ("T", "a", "a", "a"))
    return shortest_depth(inputs, goal, tuple(combinations(range(4), 2)), protected=(1, 2))


def mapped(word, sites):
    return tuple((sites[i], sites[j]) for i, j in word)


def graph_cost(logical_words, cat, ports):
    edges = {tuple(sorted(e)) for word in logical_words for i, j in word
             for e in mapped(VACANCY, (i, j, cat))}
    for k, port in enumerate(ports):
        r = cat + 1 + 2 * k
        edges.update(tuple(sorted(e)) for e in mapped(PROTECTED_METER, (port, r, r + 1, cat)))
    return {"edges": len(edges), "max_degree": max(Counter(i for e in edges for i in e).values())}


def compiled_launch(raw, logical_word, ports, checkpoints=None):
    """One native apparatus. The reference intervenes only in assertions."""
    cat = len(raw)
    state = [*(RECODE[x] for x in raw), "a", *(("b", "b") * len(ports))]
    ref = list(raw)
    for n, (i, j) in enumerate(logical_word, start=1):
        for edge in mapped(VACANCY, (i, j, cat)):
            step(state, edge)
        ref[i], ref[j] = vacancy.contact(ref[i], ref[j])
        check(state[:cat] == [RECODE[x] for x in ref] and state[cat] == "a",
              "compiled contact or catalyst disagrees at a logical boundary")
        if checkpoints and n in checkpoints:
            check(state[:cat] == checkpoints[n], "three-port hub differs from four-label reference")
    before = tuple(state[:cat + 1])
    for k, port in enumerate(ports):
        r = cat + 1 + 2 * k
        for edge in mapped(PROTECTED_METER, (port, r, r + 1, cat)):
            step(state, edge)
            check("T" not in state[r:r + 2], "marker reached a protected record cell")
        check(state[cat] == "a", "meter failed to restore the catalyst for reuse")
    check(tuple(state[:cat + 1]) == before, "detector did not restore the held data")
    pairs = tuple(tuple(state[i:i + 2]) for i in range(cat + 1, len(state), 2))
    check(all(pair in (("a", "a"), ("b", "b")) for pair in pairs), "invalid ordinary record")
    return tuple(int(first == "a") for first, _ in pairs)


def audit_two_arm():
    rows = []
    launches = controls = 0
    for source, plates, opened in product(range(2), vacancy.BITS, vacancy.BITS):
        counts = [0] * 3
        for seeds, fills in product(vacancy.BITS, repeat=2):
            tr = vacancy.trial(source, plates, opened, seeds, fills)
            marks = compiled_launch(tr.states[0], tr.word, PORTS)
            observed = (*marks[:2], sum(marks[2:]))
            check(marks == tuple(int(tr.states[-1][i] == "T") for i in PORTS),
                  "ordinary records disagree with independent port reference")
            check(observed == tr.outcome, "ordinary readout vs frozen detector")
            counts = [x + y for x, y in zip(counts, observed, strict=True)]
            launches += 1
            for replacement in ("V", "N"):
                empty = tuple(replacement if x == "T" else x for x in tr.states[0])
                check(compiled_launch(empty, tr.word, PORTS) == (0, 0, 0, 0),
                      "ordinary-only launch gave a false hit")
                controls += 1
        check(tuple(counts) == vacancy.frozen.mobile._expected(source, plates, opened),
              "two-arm aggregate")
        rows.append({"source": source, "plates": plates, "opened": opened, "counts": counts})
    return {"launches": launches, "ordinary_source_controls": controls, "rows": rows}


def audit_three_port():
    frozen = vacancy.frozen
    counts = {}
    launches = hubs = 0
    for name, edges in (("chain", frozen.CHAIN), ("triangle", frozen.TRIANGLE),
                        ("repeated", frozen.REPEATED)):
        word = tuple(e for a, b in edges for e in vacancy.switch(a, b, 3))
        matrix = []
        for source in range(3):
            row = [0] * 3
            for bits in product(range(2), repeat=3):
                raw = tuple(x for i in range(3)
                            for x in ("T" if i == source else "N", *vacancy.stock(bits[i])))
                reference = [(3 if i == source else 1, 1 + bits[i]) for i in range(3)]
                checkpoints = {}
                n = 0
                for a, b in edges:
                    reference[a], reference[b] = frozen.device((reference[a], reference[b]), "U")
                    n += len(vacancy.switch(a, b, 3))
                    checkpoints[n] = [RECODE[x] for d, e in reference
                                      for x in ("T" if d == 3 else "N", *vacancy.stock(e - 1))]
                    hubs += 1
                marks = compiled_launch(raw, word, (0, 3, 6), checkpoints)
                check(marks == tuple(int(d == 3) for d, _ in reference), "three-port exit records")
                row = [x + y for x, y in zip(row, marks, strict=True)]
                launches += 1
            matrix.append(row)
        counts[name] = matrix
    return {"launches": launches, "hubs": hubs, "counts_over_eight": counts}


def verify():
    classes = classify()
    check(len(classes) == 24 and sum(m in ("a", "b") for _, m, _ in classes) == 8,
          "unexpected anonymous involution class")
    depths = triangle_depths()
    check(depths == {"vacancy": len(VACANCY), "meter": len(METER)}, "pinned word depth")
    protected = protected_depth()
    check(protected == len(PROTECTED_METER), "pinned protected meter depth")
    two_words = [vacancy.schedule(p, o) for p, o in product(vacancy.BITS, repeat=2)]
    f = vacancy.frozen
    three_words = [tuple(e for a, b in edges for e in vacancy.switch(a, b, 3))
                   for edges in (f.CHAIN, f.TRIANGLE, f.REPEATED)]
    def max_contacts(words, meter_count):
        return max(map(len, words)) * len(VACANCY) + meter_count * len(PROTECTED_METER)

    return {
        "scope": "Finite three-label scheduled vacancy compiler with ordinary-shade output.",
        "contact_classes": len(classes),
        "local_controls": audit_local(),
        "shade_selective_classes": sum(m in ("a", "b") for _, m, _ in classes),
        "pinned_triangle_depths": depths,
        "protected_four_site_meter_depth": protected,
        "two_arm": audit_two_arm(),
        "three_port": audit_three_port(),
        "resources": {"labels": 3, "shared_restored_a_catalysts": 1, "b_standards_per_meter": 2,
                      "two_arm_meters": len(PORTS), "two_arm_sites": 2 * vacancy.STRIDE + 1 + 2 * len(PORTS),
                      "max_two_arm_contacts": max_contacts(two_words, len(PORTS)),
                      "three_port_sites": 9 + 1 + 2 * 3,
                      "max_three_port_contacts": max_contacts(three_words, 3),
                      "two_arm_graph": graph_cost(two_words, 2 * vacancy.STRIDE, PORTS),
                      "three_port_graph": graph_cost(three_words, 9, (0, 3, 6))},
        "boundary": "The data port is restored at the endpoint; T visits the shared catalyst, "
                    "never either ordinary record cell, during the five-contact measurement. "
                    "If T never moves, replacing it by a mimics every contact with b for this rule. "
                    "Records are neither new T nor pre-existing dye routing: initialized bb becomes aa "
                    "only for T. The parity of the b count is conserved: a single changed ordinary "
                    "cell with all other cells restored is impossible. The record occupies two b "
                    "standards per port; inverse readout resets them "
                    "and erases the record. Both binary plates, fresh shutter stock, shared catalyst, "
                    "scheduled fixed graph edges and this contact table are supplied. Shortest lengths "
                    "refer only to the specified graphs, inputs, outputs, rule and stocks.",
    }


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--json", action="store_true")
    args = parser.parse_args()
    report = verify()
    if args.json:
        print(json.dumps(report, indent=2))
    else:
        print(report["scope"])
        print(f"{report['contact_classes']} classes; vacancy depth {len(VACANCY)}, "
              f"protected meter depth {report['protected_four_site_meter_depth']}; "
              f"{report['two_arm']['launches']} two-arm launches "
              f"and {report['three_port']['launches']} network launches.")
        print(report["boundary"])


if __name__ == "__main__":
    main()
