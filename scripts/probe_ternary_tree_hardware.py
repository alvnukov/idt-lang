"""Compile the fixed finite ternary vacancy fixtures on installed CS trees.

Each character in a word is an externally supplied edge offer, whether or not
it changes the state. The only native write is the existing CS contact.
Run with python3 -m scripts.probe_ternary_tree_hardware [--json].
"""

import argparse
import json
from collections import Counter
from functools import lru_cache
from itertools import product

from scripts import probe_ternary_active_readout as cs
from scripts import probe_ternary_vacancy_switch as vac
from scripts.probe_eight_label_interferometer import check


def expand(digits, edges):
    return tuple(edges[int(d)] for d in digits)


@lru_cache(maxsize=256)
def star_word(x, y, h, z):
    return expand("010102102101021", ((x, h), (y, h), (h, z)))


@lru_cache(maxsize=32)
def meter_word(d, r, s, h):
    return expand("0120101202", ((d, r), (d, h), (r, s)))


PATH = ((0, 1), (1, 2), (2, 3))


def path_word(z):
    # Four sites in order (x, a, y, z). This is a local gate, not a
    # replacement of the installed high-degree tree by a line apparatus.
    return expand({"a": "2121010212102101212", "b": "0101010212102101010"}[z], PATH)


def charge(state, signs):
    return sum(s for x, s in zip(state, signs, strict=True) if x == "b")


def audit_local():
    for x, y in product("abT", repeat=2):
        u, v = cs.contact(x, y)
        check(charge((x, y), (1, -1)) == charge((u, v), (1, -1)), "local signed charge")
        check(cs.contact(u, v) == (x, y), "local undo")
        if "T" not in (x, y):
            check((u, cs.FLIP[v]) == (cs.FLIP[y], x), "blank sector is not conjugate to swap")
        pair = (y, x) if "a" in (x, y) else (x, y)
        check(cs.replay((x, y, "a", "b"), star_word(0, 1, 2, 3))[-1] ==
              (*pair, "a", "b"), "star compiler")
        for z in "ab":
            check(cs.replay((x, "a", y, z), path_word(z))[-1] ==
                  (pair[0], "a", pair[1], z), "path compiler")
    for x in "abT":
        history = cs.replay((x, "b", "b", "a"), meter_word(0, 1, 2, 3))
        shaded = "a" if x == "T" else "b"
        check(history[-1] == (x, shaded, shaded, "a") and
              all("T" not in row[1:3] for row in history), "protected clean detector")
    # A scheduler allowed to offer any edge can keep offering this one:
    # aa -> bb -> aa forever, with no idle/no-op steps.
    check(cs.replay(("a", "a"), ((0, 1),) * 2) ==
          (("a", "a"), ("b", "b"), ("a", "a")), "unguided undo cycle")


def path_search():
    """Meet in the middle: exhaustive through length 24 on these three edges only."""
    states = tuple(product("abT", repeat=4))
    index = {state: n for n, state in enumerate(states)}
    tables = tuple(bytes([index[cs.replay(state, (edge,))[-1]] for state in states]
                         + list(range(len(states), 256))) for edge in PATH)

    def ball(seed):
        seen = {seed: 0}
        front = [seed]
        for length in range(1, 13):
            next_front = []
            for row in front:
                for table in tables:
                    image = row.translate(table)
                    if image not in seen:
                        seen[image] = length
                        next_front.append(image)
            front = next_front
        return seen

    pairs = tuple(product("abT", repeat=2))
    result = {}
    for h, z in product("ab", repeat=2):
        start = ball(bytes(index[x, h, y, z] for x, y in pairs))
        goal = ball(bytes(index[y, h, x, z] if "a" in (x, y) else index[x, h, y, z]
                          for x, y in pairs))
        # All generators are involutions; a word <=24 has a midpoint in both balls.
        result[h + z] = {"shortest_within_24": min((start[k] + goal[k] for k in start.keys() & goal),
                                                   default=None),
                         "start_ball_size": len(start), "goal_ball_size": len(goal)}
    return result


def record_words(size, ports):
    for k, d in enumerate(ports):
        r = size + 2 + 2 * k
        yield r, meter_word(d, r, r + 1, size)


def resources(size, ports, words):
    h, z = size, size + 1
    installed = {(i, h) for i in range(size)} | {(h, z)}
    suffix = []
    for d, (r, meter) in zip(ports, record_words(size, ports), strict=True):
        installed.update(((d, r), (r, r + 1)))
        suffix.extend(meter)
    installed = {tuple(sorted(e)) for e in installed}
    programs = [tuple(e for i, j in word for e in star_word(i, j, h, z)) + tuple(suffix)
                for word in words]
    offered = {tuple(sorted(e)) for program in programs for e in program}
    # The rooted star plus private length-two extensions is connected by construction.
    sites = size + 2 + 2 * len(ports)
    check(offered <= installed and len(installed) == sites - 1, "physical wiring")
    return {"sites": sites, "edges": len(installed),
            "max_degree": max(Counter(i for e in installed for i in e).values()),
            "offered_edges": len(offered),
            "max_offered_degree": max(Counter(i for e in offered for i in e).values()),
            "max_contacts": max(map(len, programs))}


def launch(raw, word, ports, checkpoints=None):
    """Single physical array. Logical reference and checkpoint reads never write to it."""
    size = len(raw)
    state = [*(cs.RECODE[x] for x in raw), "a", "b", *(("b", "b") * len(ports))]
    logical = list(raw)
    for n, (x, y) in enumerate(word, 1):
        for edge in star_word(x, y, size, size + 1):
            cs.step(state, edge)
        logical[x], logical[y] = vac.contact(logical[x], logical[y])
        check(state[:size + 2] == [*(cs.RECODE[s] for s in logical), "a", "b"],
              "logical boundary or shared stock")
        if checkpoints and n in checkpoints:
            check(tuple(logical) == checkpoints[n], "three-port four-label boundary")
    before = state[:size + 2]
    for r, meter in record_words(size, ports):
        for edge in meter:
            cs.step(state, edge)
            check("T" not in state[r:r + 2], "exposed record")
        check(state[:size + 2] == before, "unrestored data or shared stock")
    marks = tuple((state[r], state[r + 1]) for r in range(size + 2, len(state), 2))
    check(marks == tuple(("a", "a") if logical[d] == "T" else ("b", "b") for d in ports),
          "ordinary record")
    return tuple(int(x == "a") for x, _ in marks)


def audit_two_arm():
    rows = []
    launches = controls = 0
    for source, plates, opened in product(range(2), vac.BITS, vac.BITS):
        counts = [0] * 3
        for seeds, fills in product(vac.BITS, repeat=2):
            reference = vac.trial(source, plates, opened, seeds, fills)
            raw = reference.states[0]
            marks = launch(raw, reference.word, cs.PORTS)
            observed = (*marks[:2], sum(marks[2:]))
            check(observed == reference.outcome, "two-arm independent trial")
            counts = [a + b for a, b in zip(counts, observed, strict=True)]
            launches += 1
            for replacement in ("V", "N"):
                check(launch(tuple(replacement if x == "T" else x for x in raw),
                             reference.word, cs.PORTS) == (0, 0, 0, 0), "ordinary-only control")
                controls += 1
        check(tuple(counts) == vac.frozen.mobile._expected(source, plates, opened), "two-arm counts")
        rows.append({"source": source, "plates": plates, "opened": opened, "counts": counts})
    words = [vac.schedule(p, o) for p, o in product(vac.BITS, repeat=2)]
    return {"rows": rows, "launches": launches, "ordinary_source_controls": controls,
            "resources": resources(2 * vac.STRIDE, cs.PORTS, words)}


def audit_three_port():
    words, counts = [], {}
    launches = hubs = 0
    ports = (0, 3, 6)
    for name, edges in (("chain", vac.frozen.CHAIN), ("triangle", vac.frozen.TRIANGLE),
                        ("repeated", vac.frozen.REPEATED)):
        word = tuple(e for a, b in edges for e in vac.switch(a, b, 3))
        words.append(word)
        matrix = []
        for source in range(3):
            row = [0] * 3
            for bits in product(range(2), repeat=3):
                old = [(3 if i == source else 1, 1 + bit) for i, bit in enumerate(bits)]

                def encoded():
                    return tuple(x for d, c in old
                                 for x in ("T" if d == 3 else "N", *vac.stock(c - 1)))

                raw, n, checkpoints = encoded(), 0, {}
                for a, b in edges:
                    old[a], old[b] = vac.frozen.device((old[a], old[b]), "U")
                    n += len(vac.switch(a, b, 3))
                    checkpoints[n] = encoded()
                    hubs += 1
                marks = launch(raw, word, ports, checkpoints)
                check(marks == tuple(int(d == 3) for d, _ in old), "three-port ordinary record")
                row = [a + b for a, b in zip(row, marks, strict=True)]
                launches += 1
            matrix.append(row)
        counts[name] = matrix
    return {"launches": launches, "hubs": hubs, "counts_over_eight": counts,
            "resources": resources(9, ports, words)}


def verify():
    audit_local()
    return {"scope": "Scheduled finite CS tree wiring; no emergent geometry or autonomous device.",
            "two_arm": audit_two_arm(), "three_port": audit_three_port(), "local_path": path_search(),
            "charge": "Across an edge aa -> bb requires w_i+w_j=0 for any conserved real "
                      "weighted b-count; all other CS changes preserve the b sites. On a "
                      "connected bipartite graph alternating signs therefore work, and an odd "
                      "cycle forces all weights zero on its connected component. Clean opposite-side "
                      "a,b exchange is impossible. With all else restored two b->a record changes "
                      "must occupy opposite sides. Complementing ordinary shades on one side "
                      "turns every blank-only edge action into a swap.",
            "boundary": "Fixed contacts, tree, stocks, external schedules and readout times are "
                        "supplied. A changing edge may be offered repeatedly, undoing itself "
                        "forever; fairness is not implied. The 19-offer local path words do "
                        "not compile the globally branched fixture onto a line. Three installed "
                        "complementary partner leaves are idle in the three-port programs."}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--json", action="store_true")
    args = parser.parse_args()
    report = verify()
    if args.json:
        print(json.dumps(report, indent=2))
    else:
        print(report["scope"])
        for key in ("two_arm", "three_port"):
            print(key, report[key]["launches"], "launches;", report[key]["resources"])
        print(report["boundary"])


if __name__ == "__main__":
    main()
