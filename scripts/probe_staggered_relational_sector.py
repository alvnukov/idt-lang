"""What remains of the staggered open-path reachability fixture without absolute bit polarity?

Keep the selected site books, directed AB/BA templates and clean BA helper
stock. Remove the two completely unoffered bits of each AB bond. For n >= 2
the remaining triple incidence is connected. Relative observations on its
spanning tree are endpoint XORs: precisely s and its GLOBAL complement have
the same observations. Each E update can be made directly on these relations.
Individual homes may not be complemented independently: this changes whether
a crossing triple is unanimous. A two-rail home's internal equality alone
has only two values, insufficient for three marks.

Clean now means the IMAGE of the original clean codes, not that an arbitrary
chosen lift has zero helpers. A projected path from code u to code v lifts,
starting at C(u), to C(v) OR the complement of C(v), including every helper.
The first case is the absolute fixture's clean relation. For the second, put
weights (1,0) on each A home, (1,-1) on B and (0,-1) on each BA helper pair.
Every allowed triple has total coefficient zero, so the weighted bit sum Q
is conserved. Its total coefficient delta = #A - #BA is 1 on A-first paths,
0 on B-first. Q(C(w)) = #T(w); complement changes Q to delta-Q. Thus the
second case requires #T(u)+#T(v)=delta. It is impossible if both endpoints
have exactly one T. This argument applies for every alternating open length
n >= 2 and uses the absolute fixture's separate soundness/completeness result.
Only the unordered values {Q,delta-Q} are intrinsic to a relative reading.
No preparation of a one-T sector, preservation of T at dirty microsteps,
first-hit agreement, autonomous readout or time law is derived.

Alternatively add one stable, unoffered reference bit and one OBSERVED
comparison to the connected data graph. Lift both the active register and
the reference together. Opposite lifts of two standard codes then have
different reference bits, so no E path crosses between them. This recovers
every absolute clean endpoint relation without choosing the reference's
absolute value. It costs a reference and comparison access (or repurposing
an idle AB bit where one exists). An isolated unread wire does not suffice.
This is a relation on the whole apparatus, not a free site-local ternary
book, a native equality meter, or a minimum over different encodings.

Run: python3 -B -m scripts.probe_staggered_relational_sector
"""

import json
from collections import Counter, defaultdict
from dataclasses import dataclass
from functools import cache
from itertools import combinations, product

from scripts import probe_staggered_binary_codebooks as native
from scripts import probe_two_helper_staggered_search as selected


def require(ok, reason):
    if not ok:
        raise ValueError(reason)


@dataclass(frozen=True)
class Layout:
    books: tuple
    width: int
    weights: tuple
    moves: tuple
    edges: tuple
    rules: tuple

    def clean(self, word, polarity=0):
        """One of the two lifts of the same clean observation (including stock)."""
        require(len(word) == len(self.books) and all(x in "Tab" for x in word)
                and polarity in (0, 1), "invalid clean word or polarity")
        x = sum(book["Tab".index(c)] << (2*i) for i, (book, c) in enumerate(zip(self.books, word)))
        return x ^ (((1 << self.width)-1) if polarity else 0)

    def observe(self, x):
        return sum((((x >> i) ^ (x >> j)) & 1) << k for k, (i, j) in enumerate(self.edges))

    def charge(self, x):
        return sum(w for i, w in enumerate(self.weights) if (x >> i) & 1)

    def neighbors(self, relations):
        """No absolute representative or reference value is consulted."""
        for uv, vw, boundary in self.rules:
            if not ((relations & uv).bit_count() % 2 or (relations & vw).bit_count() % 2):
                yield relations ^ boundary


@cache
def layout(n, phase, anchored=False):
    require(type(n) is int and n >= 2 and phase in (0, 1), "need connected n>=2 path and phase 0/1")
    books, ab, ba = selected.SELECTED
    require(ab[0] == ba[0] == 0, "different prepared helper stock")
    site_books = tuple(native.BOOKS[books[(phase+i) % 2]] for i in range(n))
    weights = [v for i in range(n) for v in ((1, -1) if (phase+i) % 2 else (1, 0))]
    triples = []
    for i in range(n-1):
        k = (phase+i) % 2
        slots = list(range(2*i, 2*i+4))
        if k:
            slots.extend((len(weights), len(weights)+1))
            weights.extend((0, -1))
        mask = (ab, ba)[k][1]
        triples.extend(tuple(slots[j] for j in t) for m, t in enumerate(selected.TRIPLES) if mask >> m & 1)
    require(sum(weights) == 1-phase and all(sum(weights[j] for j in t) == 0 for t in triples),
            "frozen signed charge not preserved")
    active_width = len(weights)
    if anchored:
        weights.append(0)
    width = len(weights)
    # Observe just a spanning tree. Root 0 names paths for computing XORs;
    # its absolute VALUE is never used for enabling or reading a relative step.
    adj = [[] for _ in range(width)]
    edges = []
    parents = list(range(width))

    def root(i):
        while i != parents[i]:
            i = parents[i]
        return i

    candidates = [e for t in triples for e in combinations(t, 2)]
    if anchored:
        candidates.append((0, active_width))
    for i, j in candidates:
        ri, rj = root(i), root(j)
        if ri != rj:
            bit = 1 << len(edges)
            edges.append((i, j))
            adj[i].append((j, bit))
            adj[j].append((i, bit))
            parents[ri] = rj
    require(len(edges) == width-1, "disconnected observation graph")
    paths, todo = {0: 0}, [0]
    for i in todo:
        for j, bit in adj[i]:
            if j not in paths:
                paths[j] = paths[i] ^ bit
                todo.append(j)
    moves = tuple(sum(1 << i for i in t) for t in triples)
    rules = tuple((paths[u] ^ paths[v], paths[v] ^ paths[w],
                   sum(1 << k for k, (a, b) in enumerate(edges) if (mask >> a ^ mask >> b) & 1))
                  for (u, v, w), mask in zip(triples, moves, strict=True))
    return Layout(site_books, width, tuple(weights), moves, tuple(edges), rules)


def pairs(n):
    return n * (n-1) // 2


@cache
def census(n, phase, anchored=False):
    """Count unordered distinct clean word pairs, retaining coincident code images."""
    g = layout(n, phase, anchored)
    labels = native.native_labels(n)
    clean = defaultdict(list)
    for w in map("".join, product("Tab", repeat=n)):
        x = g.clean(w)
        require(g.charge(x) == w.count("T") and g.observe(x) == g.observe(g.clean(w, 1)),
                "incorrect clean charge or complement lifting")
        clean[g.observe(x)].append(w)
    seen = set()
    tallies = {scope: [0, 0] for scope in ("all", "one_T")}
    for key in clean:
        if key in seen:
            continue
        seen.add(key)
        queue, found = [key], []
        for u in queue:
            found.extend(clean.get(u, ()))
            for v in g.neighbors(u):
                if v not in seen:
                    seen.add(v)
                    queue.append(v)
        for scope, (total, both) in tallies.items():
            counts = Counter(labels[w] for w in found if scope == "all" or w.count("T") == 1)
            tallies[scope] = [total + pairs(sum(counts.values())), both + sum(map(pairs, counts.values()))]
    result = {}
    for scope, (total, both) in tallies.items():
        counts = Counter(label for w, label in labels.items() if scope == "all" or w.count("T") == 1)
        result[scope] = {"missing": sum(map(pairs, counts.values()))-both, "extra": total-both}
    return result


def verify():
    rows = []
    # Pinned unordered counts include states with complemented helper stock.
    for n, extras in enumerate(((5, 1), (22, 10), (93, 17), (386, 126), (1586, 262)), 2):
        for phase, extra in enumerate(extras):
            free = census(n, phase)
            ref = census(n, phase, True)
            zero = {"missing": 0, "extra": 0}
            require(free["all"] == {"missing": 0, "extra": extra} and free["one_T"] == zero
                    and ref["all"] == ref["one_T"] == zero, "unexpected relative clean relation")
            rows.append({"n": n, "phase": phase, "delta": 1-phase, "unanchored": free, "with_reference": ref})
    ba = layout(2, 1)
    src, dest, m = ba.clean("ab"), ba.clean("ba", 1), (1 << 2) | (1 << 4) | (1 << 5)
    require(m in ba.moves and src & m == 0 and src ^ m == dest, "BA complement leakage")
    dirty = (ba.clean("Ta"), 53, ba.clean("aT"))
    require(all((u ^ v) in ba.moves and (u & (u ^ v)) in (0, u ^ v) for u, v in zip(dirty, dirty[1:]))
            and all(ba.charge(u) == 1 for u in dirty), "unaccounted apparent T at a dirty cut")
    return {"clean_pair_census": rows, "BA_zero_T_false_edge": {"from": src, "to": dest,
            "ordinary_target": ba.clean("ba"), "flip_slots": [2, 4, 5]},
            "BA_one_T_dirty_control": {"raw_path": dirty, "intermediate_home_codes": [1, 1],
                                       "intermediate_helper_stock": 3, "conserved_Q": 1},
            "charge_rule": "A: (1,0), B: (1,-1), BA helpers: (0,-1); complement sends Q to delta-Q.",
            "scope": "Fixed one-T clean endpoints; unrestricted dirty paths. No selected preparation, "
                     "site-local decoder, autonomous detector, real time or physical status."}


if __name__ == "__main__":
    print(json.dumps(verify(), sort_keys=True))
