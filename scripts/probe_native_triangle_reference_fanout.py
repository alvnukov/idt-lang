"""Share a co-located triangle reference role; do not copy the data triangle.

Run: python3 -B -O -m scripts.probe_native_triangle_reference_fanout

The B,C contact, its recorded flag, fixed C reflection, winding convention,
three path comparator and uniform seeds are supplied resources. AB and AC are
alternative readouts on *the same* A. No independent preparations, remote
frames, general cloning channel or universal quantum theory follow.
"""

from collections import Counter, defaultdict
from fractions import Fraction
from itertools import product

from scripts.probe_heralded_triangle_factory import independent, outcome
from scripts.probe_triangle_cycle_phase_axis import (
    BITS, D, K, LABELS, SETTINGS, cycle_paths, edge, extend, gain, need,
    observed_table, pairs, rank, route_block, Stock, transposition,
)
from scripts.probe_triangle_exchange_source import initialize, signed_split


def check_events(s):
    need(len(s.tickets) == len(set(s.tickets.values()))
         and set(s.tickets.values()) == pairs(s.cloud), "non-bijective event addresses")


def add_reference(prep):
    """Tensor actual heralded AB tickets with independently addressed C tickets."""
    fresh = initialize(edge(0))
    n = len(fresh.cloud)
    cloud = tuple((3 * i + j, a * b) for i, a in prep.cloud for j, b in fresh.cloud)
    out = Stock(cloud, {
        (*t, *u): (i * n + k, j * n + l)
        for t, (i, j) in prep.tickets.items() for u, (k, l) in fresh.tickets.items()
    })
    check_events(out)
    return out


def decode(i):
    h, abc = divmod(i, 27)
    a, bc = divmod(abc, 9)
    b, c = divmod(bc, 3)
    return h, (a, b, c)


def encode(h, xyz):
    a, b, c = xyz
    return 27 * h + 9 * a + 3 * b + c


def addressed_read(s, active, setting):
    """Factor a block-diagonal router by history and untouched physical rails.

    Reassemble child *addresses* (not just current totals); the new branch
    becomes the low bit of each history. Native trine reads only touch A.
    """
    if setting == K:
        need(active in ((0, 1), (0, 2), (1, 2)), "cycle needs two triangles")
        gate = cycle_paths(1, (1, 1))
    else:
        need(active == (0,) and setting in D, "trine needs A")
        gate = signed_split(transposition(setting))
    other = tuple(i for i in range(3) if i not in active)
    groups = defaultdict(list)
    pos = {}
    for address, (rail, sign) in enumerate(s.cloud):
        h, xyz = decode(rail)
        key = h, tuple(xyz[i] for i in other)
        local = xyz[active[0]] if len(active) == 1 else 3 * xyz[active[0]] + xyz[active[1]]
        pos[address] = key, len(groups[key])
        groups[key].append((local, sign))

    by_group = defaultdict(list)
    for t, (u, v) in s.tickets.items():
        key, p = pos[u]
        key2, q = pos[v]
        need(key == key2, "event crossed a spectator or history")
        by_group[key].append((t, (p, q)))
    cloud, tickets = [], {}
    counts = Counter()
    for (h, spectator), chunk in groups.items():
        raw, routes, g, _ = route_block(tuple(chunk), gate)
        need(g == gain(setting), "unexpected number of seeds")
        base = len(cloud)
        for local, sign in raw:
            b, val = divmod(local, 3 ** len(active))
            need(b in BITS, "invalid emitted flag")
            xyz = [0, 0, 0]
            for i, x in zip(other, spectator, strict=True):
                xyz[i] = x
            for i in reversed(active):
                val, xyz[i] = divmod(val, 3)
            cloud.append((encode(2 * h + b, xyz), sign))
        for t, pair in by_group[h, spectator]:
            for seed in range(g):
                p, q = routes[pair, seed]
                dest = base + p, base + q
                tickets[(*t, seed)] = dest
                history = decode(cloud[dest[0]][0])[0]
                need(cloud[dest[0]][0] == cloud[dest[1]][0] and history // 2 == h,
                     "changed prior herald or crossed output rails")
                counts[h, history % 2] += 1
    out = Stock(tuple(cloud), tickets)
    need(len(out.tickets) == len(s.tickets) * gain(setting), "lost a descendant")
    check_events(out)
    return out, counts


def fix_contact(s):
    """Uses only the contact bit (low history bit); never inspect the AB herald."""
    reflected = transposition(0)
    cloud = []
    for rail, sign in s.cloud:
        h, (a, b, c) = decode(rail)
        cloud.append((encode(h, (a, b, reflected[c] if h % 2 == 0 else c)), sign))
    out = Stock(tuple(cloud), s.tickets.copy())
    check_events(out)
    return out


def check_winding_identity():
    """Operator diagnostic only; never supplies a current or a ticket to a gate.

    The native branch difference is 3K, so the integer coefficient in the
    product identity for branch differences is -3, not -1.
    """
    gate = cycle_paths(1, (1, 1))
    difference = tuple(tuple(x-y for x,y in zip(r,t,strict=True))
                       for r,t in zip(gate[:9], gate[9:], strict=True))
    sites = tuple(product(D, repeat=3))

    def act(v, i, j):
        result = []
        for xyz in sites:
            row = difference[3*xyz[i]+xyz[j]]
            weights = []
            for a, b in product(D, repeat=2):
                src = list(xyz)
                src[i], src[j] = a, b
                weights.append(v[encode(0, src)])
            result.append(sum(x*y for x,y in zip(row, weights, strict=True)))
        return tuple(result)

    for x,y,z in product((edge(0), edge(1)), repeat=3):
        v = tuple(x[a]*y[b]*z[c] for a,b,c in sites)
        left = act(act(v, 1, 2), 0, 1)
        right = act(act(v, 0, 1), 1, 2)
        need(left == right == tuple(-3*u for u in act(v, 0, 2)), "K_AB K_BC != -K_AC")


def probe():
    check_winding_identity()
    base = observed_table()
    tables = defaultdict(dict)
    populations = {}
    for k in SETTINGS:
        source = independent(edge((k + 1) % 3 if k in D else 0), edge(0))
        prep, emitted = extend(source, k, 1)
        s = add_reference(prep)
        prior = Counter(outcome(s, p) // 27 for p in s.tickets.values())
        need(all(prior[a] == 2 * emitted[0, a] for a in BITS), "fresh reference stock")
        raw, branches = addressed_read(s, (1, 2), K)
        fixed = fix_contact(raw)
        _, locked = addressed_read(fixed, (1, 2), K)
        for a, c in product(BITS, repeat=2):
            n = branches[a, c]
            need(n > 0 and 2 * n == prior[a] * 9, "biased/missing BC branch")
            need(locked[2*a+c, 1] == 9*n and locked[2*a+c, 0] == 0, "BC not locked to minus")
            populations[k, a, c] = n

        # A new untouched C is not a reference for the AB pole.
        _, fresh = addressed_read(s, (0, 2), K)
        for a, b in product(BITS, repeat=2):
            need(2 * fresh[a, b] == prior[a] * 9, "free edge already saw the pole")
        for ref, l in product((1, 2), SETTINGS):
            active = (0, ref) if l == K else (0,)
            _, counts = addressed_read(fixed, active, l)
            for a, c, b in product(BITS, repeat=3):
                p = Fraction(counts[2*a+c, b], branches[a, c] * gain(l))
                tables[ref, c][k, a, l, b] = p
                need(p == base[k, a, l, b], "reference readout changed within a branch")
        _, no_fix = addressed_read(raw, (0, 2), K)
        for a, c, b in product(BITS, repeat=3):
            p = Fraction(no_fix[2*a+c, b], branches[a, c] * 9)
            need(p == base[k, a, K, b ^ int(c == 0)], "wrong uncorrected pole convention")
    for tab in tables.values():
        rows = [[tab[k,a,l,b] for l,b in LABELS] for k,a in LABELS]
        need(len(tab) == 64 and rank(rows) == 4, "incomplete or degenerate table")
    need(len(tables) == 4, "missing a reference or a flag")
    return base, populations


def main():
    base, pops = probe()
    print("Same addressed 8x8 table through B or C, separately at each BC flag (+,-):")
    print("Rows and columns: P0+ P0- P1+ P1- P2+ P2- K+ K-")
    for k, a in LABELS:
        print(" ".join(str(base[k,a,l,b]).rjust(3) for l,b in LABELS))
    print("Tickets at each BC flag by preparation row:", [pops[k,a,0] for k,a in LABELS])
    print("Both flags retained; corrected BC always minus; four rank-4 tables.")
    print("Without correction AC swaps its pole in the plus branch only; untouched C is fair.")
    print("Shared A, two co-located reference choices; not two independent preparations.")


if __name__ == "__main__":
    main()
