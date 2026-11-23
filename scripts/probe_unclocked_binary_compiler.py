"""Forget the binary compiler word, retain its four triple addresses.

Only a unanimous raw triple changes (000 <-> 111). A clean observation reads
every ordered two-bit home and requires *all* supplied helper bits high. An
observation never modifies the raw state. The uniform random walk used for
waiting-time questions chooses among changing triples, not arbitrary offers.
Run: python3 -m scripts.probe_unclocked_binary_compiler [--json].
"""

import argparse
import json
from collections import Counter, deque
from fractions import Fraction
from itertools import combinations, product

from scripts import probe_binary_unanimous_triples as clocked
from scripts import probe_ternary_active_readout as native


def flood(adj, start):
    seen, queue = {start}, [start]
    for u in queue:
        for v in adj[u]:
            if v not in seen:
                seen.add(v)
                queue.append(v)
    return seen


def code_partition(adj, labels):
    """Connected components intersecting the given observational cut."""
    groups = []
    unseen = set(labels)
    while unseen:
        group = unseen & flood(adj, min(unseen))
        unseen.difference_update(group)
        groups.append(tuple(sorted(labels[s] for s in group)))
    return sorted(groups)


def dirichlet(rows, size):
    """Solve the finite Dirichlet systems with shared Laplacian, exact RHSs."""
    for i in range(size):
        # Grounded undirected component Laplacian is positive definite.
        pivot = rows[i][i]
        if not pivot:
            raise ArithmeticError("component not grounded at the observation cut")
        rows[i] = [v / pivot for v in rows[i]]
        for j, row in enumerate(rows):
            if j != i and row[i]:
                scale = row[i]
                rows[j] = [v - scale*w for v, w in zip(row, rows[i])]
    return [row[size:] for row in rows]


class Gadget:
    """Assigned two-bit homes, directed slot embeddings and initialized helpers."""

    def __init__(self, sites, edges, shared=False):
        self.sites, self.edges, self.shared = sites, tuple(edges), shared
        if not self.edges or any(i == j or min(i, j) < 0 or max(i, j) >= sites
                                 for i, j in self.edges):
            raise ValueError("edges must join distinct valid homes")
        self.helpers = tuple(2*sites + (0 if shared else k) for k in range(len(self.edges)))
        self.width = max(self.helpers) + 1
        # addressed returns the frozen, scheduled word. Deduplication discards
        # order AND multiplicities: neither affects adjacency nor offer weights.
        self.masks = tuple(sorted({m for (i, j), h in zip(self.edges, self.helpers)
                                   for m in clocked.addressed(i, j, h)}))
        self.adj = [tuple(t for m in self.masks if (t := clocked.offer(s, m)) != s)
                    for s in range(1 << self.width)]
        high = sum(1 << h for h in set(self.helpers))
        self.code = {"".join(w): high | sum(clocked.CODE[c] << (2*i) for i, c in enumerate(w))
                     for w in product(clocked.CODE, repeat=sites)}
        self.labels = {s: w for w, s in self.code.items()}

    def component(self, word):
        return flood(self.adj, self.code[word])

    def partition(self):
        return code_partition(self.adj, self.labels)

    def shortest(self, start, end, *, skip_cuts=False):
        """BFS witness; optional ban on all globally clean *interior* states."""
        source, goal = self.code[start], self.code[end]
        parents, queue = {source: None}, deque([source])
        while queue:
            s = queue.popleft()
            if s == goal:
                path = []
                while s is not None:
                    path.append(s)
                    s = parents[s]
                return path[::-1]
            for t in self.adj[s]:
                if t in parents or (skip_cuts and t in self.labels and t != goal):
                    continue
                parents[t] = s
                queue.append(t)
        return None

    def wait(self, start, targets):
        """Positive-time hit law and mean changing events, or None if unreachable.

        A target may include start itself; in that case first make an actual
        change. Solve degree*u - sum(interior neighbors' u) = boundary count
        for each hit probability; for elapsed events the RHS is degree.
        """
        s = self.code[start]
        if not self.adj[s]:
            return None
        component = self.component(start)
        cut = sorted(component & {self.code[w] for w in targets})
        if not cut:
            return None
        interior = sorted(component - set(cut))
        index, target_index = ({u: i for i, u in enumerate(part)} for part in (interior, cut))
        n, m = len(interior), len(cut)
        rows = []
        for i, u in enumerate(interior):
            deg = len(self.adj[u])
            row = [Fraction(0)] * (n + m + 1)
            row[i] = row[-1] = Fraction(deg)
            for v in self.adj[u]:
                if v in index:
                    row[index[v]] -= 1
                else:
                    row[n + target_index[v]] += 1
            rows.append(row)
        solved = dirichlet(rows, n)
        out = [Fraction(0)] * (m+1)
        # First mandatory step handles source-as-target and ordinary hits alike.
        for t in self.adj[s]:
            if t in target_index:
                out[target_index[t]] += 1
            else:
                out = [a+b for a, b in zip(out, solved[index[t]])]
        deg = len(self.adj[s])
        probs = {self.labels[t]: v/deg for t, v in zip(cut, out) if v}
        return probs, 1 + out[-1]/deg


def compare(g):
    """Compare clean-code equivalence, not one-step or paced simulation."""
    def moves(w):
        for i, j in g.edges:
            u = list(w)
            u[i], u[j] = native.contact(u[i], u[j])
            yield "".join(u)

    native_groups = code_partition({w: tuple(moves(w)) for w in g.code}, {w: w for w in g.code})
    raw_groups = g.partition()
    native_pairs, raw_pairs = ({p for group in groups for p in combinations(group, 2)}
                               for groups in (native_groups, raw_groups))
    return {"sites": g.sites, "raw_bits": g.width, "raw_states": len(g.adj),
            "clean_codes": len(g.code), "pair_count": len(g.code)*(len(g.code)-1)//2,
            "native_components": len(native_groups), "raw_code_components": len(raw_groups),
            "losses": sorted(native_pairs - raw_pairs), "extras": sorted(raw_pairs - native_pairs)}


def waited(g, start, targets):
    result = g.wait(start, targets)
    if result is None:
        return None
    probs, mean = result
    return {"probabilities": {k: str(v) for k, v in probs.items()}, "mean_changes": str(mean)}


def triples(mask, width):
    return tuple(i for i in range(width) if mask & (1 << i))


def compact(c):
    counts = Counter("-".join(map(str, sorted((u.count("T"), v.count("T")))))
                     for u, v in c["extras"])
    return {**c, "losses": len(c["losses"]), "extras": len(c["extras"]),
            "extras_by_hole_counts": dict(sorted(counts.items()))}


def verify():
    local = Gadget(2, ((0, 1),))
    local_rows = {}
    for start in local.code:
        comp = local.component(start)
        distinct = sorted(local.labels[t] for t in comp if t in local.labels
                          and t != local.code[start])
        local_rows[start] = {
            "distinct_endpoints": distinct, "component_raw_size": len(comp),
            "degrees": dict(sorted(Counter(len(local.adj[t]) for t in comp).items())),
            "next_clean": waited(local, start, local.code),
            "next_distinct": waited(local, start, distinct)}

    orientations = []
    joined = {}
    for shared in (False, True):
        forward_masks = Gadget(3, ((0, 1), (1, 2)), shared).masks
        for rev in product((False, True), repeat=2):
            edges = tuple((i+1, i) if r else (i, i+1) for i, r in enumerate(rev))
            g = Gadget(3, edges, shared)
            c = compare(g)
            orientations.append({"edges": edges, "shared": shared, **compact(c),
                                 "same_addresses_as_forward": g.masks == forward_masks,
                                 "extra_pairs": c["extras"]})
            if any(rev):
                continue
            first_paths = []
            for u, v in c["extras"]:
                path = g.shortest(u, v, skip_cuts=True)
                first_paths.append({"from": u, "to": v, "raw_path": path,
                                    "triples": None if path is None else
                                    [triples(x^y, g.width) for x,y in zip(path, path[1:])]})
            joined["shared" if shared else "private"] = {
                "edges": edges, "helpers": g.helpers, "extra_first_clean_paths": first_paths,
                "representative_waits": {
                    w: {"next_clean": waited(g, w, g.code),
                        "next_distinct": waited(g, w, set(g.code)-{w}),
                        "target": t, "hit_target": waited(g, w, {t})}
                    for w,t in (("TTT", "aaa"), ("bTT", "TTb"), ("baT", "Tab"))}}

    holdouts = []
    for n in (4, 5):
        path_edges = tuple((i, i+1) for i in range(n-1))
        private = Gadget(n, path_edges)
        benchmark = private.partition()
        for g in (private, Gadget(n, path_edges, shared=True)):
            holdouts.append({"edges": g.edges, "helpers": g.helpers, **compact(compare(g)),
                             "same_clean_partition_as_private": g.partition() == benchmark})
    disjoint = Gadget(4, ((0, 1), (2, 3)))
    return {"scope": "Finite reachability at clean global cuts, with no compiler word.",
            "local_masks": [triples(m, local.width) for m in local.masks],
            "local_raw_states": len(local.adj), "local": local_rows, "orientations": orientations,
            "joined_forward": joined, "forward_path_holdouts": holdouts,
            "disjoint_private": compact(compare(disjoint)),
            "boundaries": [
                "Homes, pair code T=0/a=1/b=2, addresses, helpers initially high and cut are supplied.",
                "A changing triple adds/removes three ones. At clean cuts weight = helpers + sites - #T.",
                "The hole-count residue is conserved; its exact count need not be. These are logical holes.",
                "On a single active star, target time/2 is geometric(1/4); "
                "waiting is unbounded and adversarial choices can avoid the target indefinitely.",
                "Waiting laws assume uniform choices among changing edges, not an intrinsic clock or probability.",
                "No derivation of physical space, particle species, measurement apparatus or quantum dynamics."]}


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--json", action="store_true")
    args = parser.parse_args()
    report = verify()
    if args.json:
        print(json.dumps(report, indent=2))
    else:
        print(report["scope"])
        print("Local clean partition:", Gadget(2, ((0, 1),)).partition())
        for layout, row in report["joined_forward"].items():
            first = next(p for p in row["extra_first_clean_paths"] if (p["from"], p["to"]) == ("TTT", "aaa"))
            print(layout, "TTT -> aaa first return:", first["raw_path"], "triples:", first["triples"])
            print(layout, "TTT waits:", row["representative_waits"]["TTT"])
        for r in report["forward_path_holdouts"]:
            print("Path sites, bits, native/raw groups, lost/extra pairs:",
                  *(r[k] for k in ("sites", "raw_bits", "native_components", "raw_code_components", "losses", "extras")))
        print(*report["boundaries"], sep="\n")
