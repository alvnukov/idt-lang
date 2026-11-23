"""Literal ternary vacancy contacts on fixed finite graphs. Run as a module.

V is vacant, N is occupied, and T is occupied with a conserved dye. Meters
count T, not ordinary occupancy. The timings, filled data baseline and clean
complementary control stock are supplied; there is no alphabet-minimality,
autonomous detector, resource dominance, or quantum reconstruction claim.
"""

import argparse
import json
from collections import Counter, defaultdict
from dataclasses import dataclass
from itertools import product

from scripts import probe_vacuum_compensated_network as frozen
from scripts.probe_eight_label_interferometer import check

BITS = tuple(product(range(2), repeat=2))
# Per arm: data, vacancy control, plate partner, data dump, data refill,
# control refill/dump, partner refill/dump, scratch vacancy.
D, C, Q, DUMP, FILL, RC, RQ, S = range(8)
STRIDE = 8


def contact(a, b):
    return (b, a) if (a == "V") != (b == "V") else (a, b)


def occupancy(state):
    return tuple(x != "V" for x in state)


def replay(raw, word):
    state = list(raw)
    states = [tuple(state)]
    for a, b in word:
        state[a], state[b] = contact(state[a], state[b])
        states.append(tuple(state))
    return tuple(states)


def triangle(a, b, c):
    return ((a, c), (a, b), (b, c))


def switch(a, b, stride):
    i, j = stride * a, stride * b
    return triangle(i + D, j + D, i + C) + triangle(i + D, j + D, j + C)


def stock(bit):
    return ("V", "N") if bit == 0 else ("N", "V")


def shutter(i):
    return (
        ((i + D, i + DUMP), (i + D, i + FILL))
        + triangle(i + C, i + RC, i + S)
        + triangle(i + Q, i + RQ, i + S)
    )


def schedule(plates, opened):
    hub = switch(0, 1, STRIDE)
    middle = tuple((i + C, i + Q) for arm, i in enumerate((0, STRIDE)) if plates[arm])
    for arm, i in enumerate((0, STRIDE)):
        if not opened[arm]:
            middle += shutter(i)
    return hub + middle + hub


@dataclass(frozen=True)
class Trial:
    states: tuple
    word: tuple

    def record(self, arm):
        i = arm * STRIDE
        return tuple(self.states[-1][i + j] for j in (DUMP, RC, RQ))

    @property
    def outcome(self):
        final = self.states[-1]
        return (
            int(final[D] == "T"),
            int(final[STRIDE + D] == "T"),
            sum(self.record(i).count("T") for i in range(2)),
        )


def trial(source, plates, opened, seeds, fills):
    raw = tuple(
        x
        for i in range(2)
        for x in ("T" if i == source else "N", *stock(seeds[i]), "V", "N", *stock(fills[i]), "V")
    )
    word = schedule(plates, opened)
    return Trial(replay(raw, word), word)


def network(source, bits, edges):
    # No between-hub reset: these nine physical sites persist throughout.
    raw = tuple(x for i in range(3) for x in ("T" if i == source else "N", *stock(bits[i])))
    for a, b in edges:
        raw = replay(raw, switch(a, b, 3))[-1]
        yield tuple(raw[i : i + 3] for i in (0, 3, 6))


def audit_local():
    for a, b in product("VNT", repeat=2):
        out = contact(a, b)
        check(occupancy(out) == occupancy((b, a)), "occupancy is not the transposition factor")
        check(contact(*out) == (a, b) and sorted(out) == sorted((a, b)), "contact conservation")
        check(replay((a, b, "V"), triangle(0, 1, 2))[-1] == (b, a, "V"), "vacant scratch swap")
        check(
            tuple(x for x in out if x != "V") == tuple(x for x in (a, b) if x != "V"),
            "adjacent contact overtook the occupied subsequence",
        )
    check(
        replay(("T", "N", "V"), triangle(0, 1, 2))[-1] == ("N", "T", "V"),
        "triangle overtaking witness",
    )
    # Saturate both controls and both partners, keeping both data occupied.
    for d, e in product("NT", repeat=2):
        raw = (d, "N", "N", e, "N", "N")
        check(all(st == raw for st in replay(raw, switch(0, 1, 3))), "full control moved")


def audit_two_arm():
    launches = erases = same_history = 0
    rows = []
    for source, plates, opened in product(range(2), BITS, BITS):
        counted = [0, 0, 0]
        for seeds, fills in product(BITS, repeat=2):
            tr = trial(source, plates, opened, seeds, fills)
            path = source ^ seeds[0] ^ seeds[1]
            check(replay(tr.states[-1], tr.word[::-1]) == tr.states[::-1], "reverse history")
            check(sum(tr.outcome) == 1 and tr.outcome[2] == int(not opened[path]), "loss")
            for i in range(2):
                tag = "T" if i == path else "N"
                old = (tag, *stock(seeds[i] ^ plates[i]))
                refill = ("N", *stock(fills[i]))
                j = i * STRIDE
                # Last six contacts are the analyzer. Pin every single site at
                # its input: not just the record tag, parity, or exit meter.
                expected = (
                    (*old, "V", "N", *stock(fills[i]), "V")
                    if opened[i]
                    else (*refill, tag, "V", *old[1:], "V")
                )
                check(tr.states[-7][j : j + STRIDE] == expected, "shutter boundary")
                if not opened[i] and not plates[i]:
                    flip = tuple(1 if k == i else x for k, x in enumerate(plates))
                    alt = trial(source, flip, opened, seeds, fills)
                    changed = {
                        k for k, (x, y) in enumerate(zip(tr.states[-1], alt.states[-1])) if x != y
                    }
                    check(
                        changed == {j + RC, j + RQ} and alt.outcome == tr.outcome,
                        "closed plate not isolated to complementary record",
                    )
                    erases += 1
            if source == 0:
                other = trial(1, plates, opened, seeds, fills)
                check(
                    all(
                        occupancy(a) == occupancy(b)
                        for a, b in zip(tr.states, other.states, strict=True)
                    ),
                    "binary history distinguished the two dyes",
                )
                same_history += 1
            launches += 1
            counted = [a + b for a, b in zip(counted, tr.outcome, strict=True)]
        expected = frozen.mobile._expected(source, plates, opened)
        check(tuple(counted) == expected, "two-arm setting row")
        rows.append({"source": source, "plates": plates, "opened": opened, "counts": counted})
    return {
        "launches": launches,
        "rows": rows,
        "pinned_dump_interventions": erases,
        "equal_source_occupancy_histories": same_history,
    }


def audit_network():
    launches = hubs = 0
    counts = {}
    for name, edges in (
        ("chain", frozen.CHAIN),
        ("triangle", frozen.TRIANGLE),
        ("repeated", frozen.REPEATED),
    ):
        matrix = []
        for source in range(3):
            row = Counter()
            for bits in product(range(2), repeat=3):
                old = [(3 if i == source else 1, 1 + b) for i, b in enumerate(bits)]
                for after, (a, b) in zip(network(source, bits, edges), edges, strict=True):
                    old[a], old[b] = frozen.device((old[a], old[b]), "U")
                    encoded = tuple(("T" if d == 3 else "N", *stock(e - 1)) for d, e in old)
                    check(
                        all(d in (1, 3) and e in (1, 2) for d, e in old) and after == encoded,
                        "prepared raw projector disagrees with frozen four-label U",
                    )
                    hubs += 1
                row.update(i for i, (d, c, q) in enumerate(after) if d == "T")
                launches += 1
            matrix.append(tuple(row[i] for i in range(3)))
        counts[name] = tuple(matrix)
    return {"launches": launches, "compared_hubs": hubs, "counts_over_eight": counts}


def verify():
    audit_local()
    word = schedule((1, 1), (0, 0))  # union of all setting edges
    nbrs = defaultdict(set)
    for a, b in word:
        nbrs[a].add(b)
        nbrs[b].add(a)
    return {
        "scope": "Finite prepared dye-routing fixture, not ordinary occupancy detection.",
        "two_arm": audit_two_arm(),
        "network": audit_network(),
        "resources": {
            "raw_labels": 3,
            "two_arm_sites": 16,
            "three_port_sites": 9,
            "max_two_arm_contacts": len(word),
            "max_two_arm_degree": max(map(len, nbrs.values())),
        },
        "boundary": "For each raw pair, binary occupancy transposes exactly. By "
        "composition, any fixed contact word permutes the launch occupancy, "
        "even with common ancillas. Different placement or replacement of T by N "
        "cannot signal in that history. Ordered colored outputs can distinguish "
        "them. Adjacent contacts preserve occupied order on a fixed linear path; "
        "a triangle can swap T,N and restore its vacancy. Supplied timing, "
        "graph, full D baseline, dye readout and clean stock are not derived.",
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
        print(
            f"{len(report['two_arm']['rows'])} setting rows, {report['two_arm']['launches']} "
            f"launches; {report['network']['compared_hubs']} three-port hub comparisons."
        )
        print(report["boundary"])


if __name__ == "__main__":
    main()
