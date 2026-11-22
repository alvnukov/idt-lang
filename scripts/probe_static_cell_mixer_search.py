"""Can a static three-store petal do the programmed packet mixer's work?

PRIMARY: all 40^3 ordered triples of fixed, local, reciprocal, count-
conserving side/mobile-bit/store-bit tables. On six forward two-of-four
preparations, ask for set complement after a fixed four-cycle of the
addressed slots. Keep the original TURN and the six possible orders apart.
The hub is transparent. No bypass command, launch-sector selection after
the fact, or input-dependent number of visits. Close the first-return
permutation orbit to cover every common positive return count. Re-run
with reverse launch side; dropping direction reset is a separate control.

SECONDARY: inspect complement after *any* wire permutation. Sixteen
assemblies realize pure set complement F^3, including X-S-X, where S is
the straight bit swap and X swaps while reflecting on unequal bits. This
is NOT the requested complement plus a four-cycle. No ordering of output
names is an extra physical wire operation. At fixed trial number, pure
complement just flips the sign of centered occupancy counts.

The physical graph and passive hub contacts remain supplied. For X-S-X
the third return is exactly 32 physical hops after launch on every
two-mark input. A single memoryless return-side/lane report cannot tell
the third return from earlier ones. Reading at a chosen time, keeping
phase or logging the return history is not a derived stop flag. The cost
is cursor edge crossings, not summed mobile mark flux or detector work.
Singletons are reported independently, not fitted or used in selection.

Lossless enumeration recipe: sorted lexicographic eight-output table
codes; assembly id = 1600*left + 40*middle + right (zero-based). Use
--id NUMBER to replay any accepted OR rejected assembly. Default verifies
the full census and compares selected triples against the physical mesh.
Run: python3 -B -O -m scripts.probe_static_cell_mixer_search
"""

import argparse
import json
from collections import Counter
from functools import cache
from itertools import combinations, permutations, product

from scripts.probe_mobile_cell_complement_mixer import EDGES, TURN, Petal, need
from scripts.probe_reversible_cell_census import inferred_rule, involutions


def mask(occupied):
    return sum(1 << i for i in occupied)


PAIRS = tuple(mask(e) for e in EDGES)
ONES = (1, 2, 4, 8)
LAWS = tuple(sorted(r for r in involutions(8) if
                    all((z & 3).bit_count() == (r[z] & 3).bit_count() for z in range(8))))
PERMS = tuple(permutations(range(4)))
CYCLES = tuple(p for p in PERMS if len({0, p[0], p[p[0]], p[p[p[0]]]}) == 4)
COMPS = {tuple(PAIRS.index(15 ^ mask(p[j] for j in e)) for e in EDGES): p for p in PERMS}
GOALS = {row: p for row, p in COMPS.items() if p in CYCLES}
IDENTITY = tuple(range(4))
S, X, D = (LAWS.index(inferred_rule(a, c)) for a, c in ((0,0), (1,0), (0,1)))


def law_code(j):
    return "".join(map(str, LAWS[j]))


def assembly_id(triple):
    a, b, c = triple
    return 1600*a + 40*b + c


def decode(key):
    if not 0 <= key < 64000:
        raise ValueError("assembly id must be in 0..63999")
    a, rem = divmod(key, 1600)
    b, c = divmod(rem, 40)
    return a, b, c


@cache
def columns(masks):
    """Fixed lookup per site and rule; state index is direction*n + mask index."""
    built = []
    for j in range(1,4):
        rows = []
        for r in LAWS:
            one = []
            for d, m in product((0,1), masks):
                z = r[4*d + 2*(m & 1) + ((m >> j) & 1)]
                d_out = int((z & 4) == 0)
                out = (m & ~(1 | 1 << j)) | ((z >> 1) & 1) | ((z & 1) << j)
                one.append(len(masks)*d_out + masks.index(out))
            rows.append(tuple(one))
        built.append(tuple(rows))
    return tuple(built)


def first_returns(triple, masks):
    n = len(masks)
    maps = [c[r] for c, r in zip(columns(masks), triple, strict=True)]
    ports, hops = [], []
    for s in range(2*n):
        x, t = (1 if s < n else 3), 1
        while 1 <= x <= 3:
            s = maps[x-1][s]
            x += 1 if s < n else -1
            t += 1
            need(t <= 3*2*n+1, "more visits than distinct internal contact states")
        ports.append(s)
        hops.append(4*t)  # equal four-edge subdivisions of every logical wire
    need(set(ports) == set(range(2*n)), "hub first-return map is not a permutation")
    return tuple(ports), tuple(hops)


@cache
def inspect_powers(f, reverse):
    offset = 6*int(reverse)
    start = tuple(range(offset, offset+6))
    row, detail = start, []
    while True:
        row = tuple(f[j] for j in row)
        packet = tuple(j % 6 for j in row)
        reset = all(j//6 == int(reverse) for j in row)
        matches = max(sum(x == y+offset for x, y in zip(row, goal)) for goal in GOALS)
        detail.append((reset, COMPS.get(packet), matches))
        if row == start:
            return tuple(detail)


class StaticMesh(Petal):
    def __init__(self, triple):
        self.triple = triple
        super().__init__(LAWS[triple[0]], False)

    def scatter(self, v, ingress, stored):
        if v not in self.cells:
            return super().scatter(v, ingress, stored)
        bit, ports, back = self.cells[v]
        side, lane = back[ingress]
        r = LAWS[self.triple[bit.bit_length()-1]]
        code = r[4*int(side == 1) + 2*lane + int(bool(stored & bit))]
        new_stock = (stored | bit) if code & 1 else (stored & ~bit)
        return ports[1 if code & 4 else -1, (code >> 1) & 1], new_stock


def physical_check(triple):
    g = StaticMesh(triple)
    for weight in range(5):
        slots = tuple(combinations(range(4),weight))
        masks = tuple(map(mask, slots))
        f, hops = first_returns(triple, masks)
        for i, (d, e) in enumerate(product((1,-1), slots)):
            (new_d, out), t = g.physical_return(d, e)
            index = len(slots)*int(new_d == -1) + slots.index(out)
            need((index, t) == (f[i], hops[i]), "physical mesh disagrees")


def journey(f, hops, start, n, count):
    out = []
    i = start
    for _ in range(count):
        cost, i = hops[i], f[i]
        out.append((1 if i < n else -1, i % n, cost))
    return out


def replay(triple):
    f, hops = first_returns(triple, PAIRS)
    fs, ts = first_returns(triple, ONES)
    return {"id": assembly_id(triple), "site_indices": triple,
            "local_table_codes": tuple(map(law_code, triple)),
            "packet_order": EDGES, "state_order": "all positive then all negative",
            "weight_two_first_returns": f, "weight_two_physical_hops": hops,
            "power_fields": "direction restored; complement turns (null if none); best exact primary rows/6",
            "forward_powers": inspect_powers(f,False), "reverse_powers": inspect_powers(f,True),
            "singleton_first_returns": fs, "singleton_physical_hops": ts}


def secondary_checks(tr, f, h):
    fs, ts = first_returns(tr, ONES)
    # The target was defined only on weight two. All sixteen secondary
    # winners fail even to restore direction on ANY forward singleton at k=3.
    need(all(journey(fs, ts, i, 4, 3)[-1][0] == -1 for i in range(4)), "singleton holdout")
    cal = {}
    for i in range(12):
        path = journey(f,h,i,6,3)
        d, out, _ = path[-1]
        need(d == (1 if i < 6 else -1) and PAIRS[out] == (15 ^ PAIRS[i % 6])
             and sum(v[2] for v in path) == 32, "physical complement calendar")
        cal[i] = path
    # Even knowing initial lane, a memoryless reader cannot distinguish
    # the first vs third return for this actual input.
    if tr == (X,S,X):
        local = [(d, PAIRS[j] & 1) for d,j,_ in cal[0]]
        need(local[0] == local[2] == (1,0), "local stopping countercontrol")
        # A calibrated logger can distinguish all six ENABLED preparations
        # from launch lane and first TWO return sides, with no hidden stores.
        records = {(PAIRS[i] & 1, cal[i][0][0], cal[i][1][0]) for i in range(6)}
        need(len(records) == 6, "hub history is not sufficient for packet identification")


def census():
    need(len(LAWS) == 40 and len(GOALS) == 6 and TURN in CYCLES, "census scope")
    periods, near, singles, secondary, primary = Counter(), Counter(), Counter(), [], Counter()
    maps = set()
    for tr in product(range(40), repeat=3):
        f, h = first_returns(tr, PAIRS)
        fs, _ = first_returns(tr, ONES)
        maps.add(f)
        need(all(f[(f[(i+6) % 12]+6) % 12] == i for i in range(12)), "time reversal")
        for rev in (False, True):
            rows = inspect_powers(f, rev)
            periods[rev, len(rows)] += 1
            if not rev:
                near["one", rows[0][2]] += 1
                near["ever", max(m for _,_,m in rows)] += 1
            flags = set()
            for k, (reset, p, _) in enumerate(rows, 1):
                if p in CYCLES:
                    for when in (("ever","one") if k == 1 else ("ever",)):
                        for target in (("any","original") if p == TURN else ("any",)):
                            flags.add((rev, when, target, "ignore direction"))
                            if reset:
                                flags.add((rev, when, target, "reset direction"))
                if reset and p is not None:
                    need(p == IDENTITY and k == 3, "secondary complement class changed")
                    if not rev:
                        secondary.append(tr)
                        secondary_checks(tr, f, h)
            primary.update(flags)
            offset = int(rev)*4
            single = fs[offset:offset+4]
            if all(v//4 == int(rev) for v in single):
                singles[rev, "reset"] += 1
                if tuple(x % 4 for x in single) in CYCLES:
                    singles[rev, "wire four-cycle"] += 1
    expected = {(a,b,c) for a in (30,31) for b in (18,19,38,39) for c in (23,31)}
    need(not primary and len(secondary) == 16 and set(secondary) == expected, "census outcome")
    need(len(maps) == 960, "number of distinct weight-two first-return maps")
    for rev in (False, True):
        need({k: v for (d,k),v in periods.items() if d == rev} ==
             {1:1,2:20514,3:16,4:32251,6:4810,8:796,12:5612}, "period census")
        need((singles[rev,"reset"], singles[rev,"wire four-cycle"]) == (64,8), "singleton counts")
    need({i:n for (w,i),n in near.items() if w == "one"} == {0:41165,1:19632,2:2912,3:260,4:31}
         and {i:n for (w,i),n in near.items() if w == "ever"} == {2:38303,3:9872,4:15825},
         "closest forward primary matches")
    survivors = {LAWS.index(inferred_rule(a,c)) for a,c in product(range(2), repeat=2)}
    need({v for v in secondary if set(v) <= survivors} == {(X,S,X),(X,D,X)}, "timing survivors")
    for tr in {*secondary, (0,0,0), (S,S,S), (39,1,39), (1,22,7)}:
        physical_check(tr)
    print("64000 static conservative reciprocal triples; 960 distinct two-mark first-return maps. "
          "Primary complement + original/any four-cycle: 0/64000, one/any common count, "
          "both launch directions, even ignoring output direction. Best forward exact score 4/6.")
    print("Secondary pure complement: 16/64000 at three returns, never one. All-six/all-orientation "
          "time 32 physical hops for these devices. Only X-S-X and X-D-X use all prior timing "
          f"survivors (ids {assembly_id((X,S,X))}, {assembly_id((X,D,X))}). "
          "No original-target hit or physical output wire turn.")
    print("Both directions separately: 64/64000 restore all singleton directions at one passage, "
          "8/64000 also rotate their four wires. At three passages every secondary winner reverses "
          "every forward singleton's direction. X-S-X needs a clock/history for completion; "
          "no present side/lane flag. IDs 0..63999 retain every rejection.")


def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument("--id", type=int, help="replay one exact assembly and all powers through recurrence")
    args = p.parse_args()
    if args.id is None:
        census()
    else:
        tr = decode(args.id)
        physical_check(tr)
        print(json.dumps(replay(tr), separators=(",",":")))


if __name__ == "__main__":
    main()
