"""Do two free gaits remain a decomposition of four evolving raw bonds?

The imported event rule sees only incident marked bonds. A *reading* is a
perfect matching of two short and two long bonds into two isolated active
gaits. No matching is selected, stored, or used to generate a successor.
Distances count individual offered events; histories have no assumed weight.

Run: python3 -m scripts.probe_two_packet_matchings
"""

from __future__ import annotations

import json
from collections import Counter, deque
from functools import cached_property
from itertools import combinations, product
from math import comb
from random import Random

if __package__:
    from .probe_conserved_bond_gait import (
        Move,
        Ports,
        cycle_square,
        fixture,
        link,
        need,
        offers,
    )
else:
    from probe_conserved_bond_gait import (
        Move,
        Ports,
        cycle_square,
        fixture,
        link,
        need,
        offers,
    )


def matching_oracle(n):
    """Independent cyclic interval count, not a distribution on preparations.

    Each of n long bonds meets six active short partners; each short meets
    six long partners. Choose two such compatibilities and remove the pairs
    sharing a bond. This counts a double reading twice. A double reading is
    a four-cycle: choose two long bonds and two common compatible shorts.
    Counting ordered long-bond separations d and dividing by two corrects
    for the two ways to name the first long bond. For n >= 11 opposite
    tails do not overlap, giving 20n double and n(18n - 73) single
    readings, conditional on the six-consecutive-partner premise.
    """
    if n < 7:
        raise ValueError("interval oracle is for n >= 7")
    q = (max(0, 6 - d) + max(0, 6 - (n - d)) for d in range(1, n))
    double = n * sum(comb(k, 2) for k in q) // 2
    single = comb(6 * n, 2) - 2 * n * comb(6, 2) - 2 * double
    return comb(n, 2) ** 2 - single - double, single, double


def isolated_table(ports):
    table = {}
    for s, t in product(ports.short_links, ports.motifs):
        moves = offers(ports, frozenset((s, t)))
        if moves:
            need(len(moves) == 1, "isolated active gait is not deterministic")
            table[s, t], = moves
    return table


def readings(table, short, long):
    a, b = short
    c, d = long
    return tuple(p for p in (((a, c), (b, d)), ((a, d), (b, c)))
                 if all(pair in table for pair in p))


def move_key(m):
    return m.center, tuple(sorted(m.old)), tuple(sorted(m.new))


def state_record(state):
    return sorted(sorted(edge) for edge in state)


def bfs(edges, start):
    """All raw successors, preserving one full move for each first visit."""
    parents, distances, queue = {start: None}, {start: 0}, deque([start])
    while queue:
        s = queue.popleft()
        for m, t in edges[s]:
            if t not in parents:
                parents[t] = (s, m)
                distances[t] = distances[s] + 1
                queue.append(t)
    return parents, distances


def components(edges, reverse):
    """Iterative Kosaraju; only the classification uses reverse arrows."""
    visited, finish = set(), []
    for s in range(len(edges)):
        if s in visited:
            continue
        visited.add(s)
        stack = [(s, iter(edges[s]))]
        while stack:
            u, neighbors = stack[-1]
            nxt = next(neighbors, None)
            if nxt is None:
                stack.pop()
                finish.append(u)
            else:
                _, t = nxt
                if t not in visited:
                    visited.add(t)
                    stack.append((t, iter(edges[t])))
    owner, groups = {}, []
    for s in reversed(finish):
        if s in owner:
            continue
        i = len(groups)
        group, queue = [], [s]
        owner[s] = i
        while queue:
            u = queue.pop()
            group.append(u)
            for t in reverse[u]:
                if t not in owner:
                    owner[t] = i
                    queue.append(t)
        groups.append(group)
    bottom = [all(owner[t] == i for s in group for _, t in edges[s])
              for i, group in enumerate(groups)]
    return groups, owner, bottom


def reverse_distance(reverse, targets):
    """Exact minimum legal forward distance to the set; -1 means unreachable."""
    dist = [-1] * len(reverse)
    queue = deque(targets)
    for s in queue:
        dist[s] = 0
    while queue:
        s = queue.popleft()
        for t in reverse[s]:
            if dist[t] == -1:
                dist[t] = dist[s] + 1
                queue.append(t)
    return dist


class Shell:
    def __init__(self, n):
        if n < 7:
            raise ValueError("carrier requires n >= 7")
        self.n = n
        self.graph = cycle_square(n)
        self.ports = Ports.from_graph(self.graph)
        self.table = isolated_table(self.ports)
        # Validate the coordinate oracle only after constructing raw incidence.
        expected = {(link(j % n, (j + 1) % n), link(i, (i + 2) % n))
                    for i in range(n) for j in range(i - 2, i + 4)}
        need(self.table.keys() == expected, "six-partner interval oracle disagrees")
        self.states = [frozenset((*s, *t)) for s, t in product(
            combinations(self.ports.short_links, 2), combinations(self.ports.motifs, 2))]
        self.index = {state: i for i, state in enumerate(self.states)}
        self.edges, self.kind = [], []
        self.reverse = [[] for _ in self.states]
        self.degree = [Counter(), Counter(), Counter()]
        differences = Counter()
        for i, state in enumerate(self.states):
            pairings = self.matchings(state)
            k = len(pairings)
            self.kind.append(k)
            raw = offers(self.ports, state)
            if pairings:
                predicted = {self.table[p] for reading in pairings for p in reading
                             if self.table[p].new not in state}
                need(predicted <= raw, "a complete reading predicted a nonexistent move")
                if predicted != raw:
                    differences[k] += 1
            row = [(m, self.index[m.apply(state)]) for m in sorted(raw, key=move_key)]
            need(len({t for _, t in row}) == len(raw), "distinct moves conflated")
            self.edges.append(row)
            self.degree[k][len(raw)] += 1
            for _, t in row:
                self.reverse[t].append(i)
        self.counts = tuple(self.kind.count(k) for k in range(3))
        self.mismatches = differences[1], differences[2]
        need(self.counts == matching_oracle(n), "combinatorial census disagrees")

    def matchings(self, state):
        short = state & self.ports.short_links
        return readings(self.table, short, state - short)

    def check_relabeling(self):
        """Independently recompile the ports, readings and offers on opaque names."""
        names = [f"alias-{i}" for i in range(self.n)]
        Random(501 + self.n).shuffle(names)
        ports = Ports.from_graph({names[i]: frozenset(names[v] for v in self.graph[i])
                                  for i in reversed(self.graph)})
        edge = {e: frozenset(names[v] for v in e)
                for e in self.ports.short_links | self.ports.motifs.keys()}
        table = isolated_table(ports)
        for i, state in enumerate(self.states):
            other = frozenset(edge[e] for e in state)
            short = other & ports.short_links
            lhs = {frozenset((edge[s], edge[t]) for s, t in p)
                   for p in self.matchings(state)}
            rhs = {frozenset(p) for p in readings(table, short, other - short)}
            need(lhs == rhs, "relabeling changed which matchings are legal")
            need({Move(names[m.center], edge[m.old], edge[m.new]) for m, _ in self.edges[i]}
                 == offers(ports, other), "relabeling changed raw offers")
        return len(self.states)

    @cached_property
    def scc(self):
        return components(self.edges, self.reverse)

    @cached_property
    def return_ranks(self):
        return {key: reverse_distance(self.reverse, (i for i in range(len(self.states)) if accept(i)))
                for key, accept in (
                    ("pairable", lambda i: self.kind[i] > 0),
                    ("unique", lambda i: self.kind[i] == 1),
                    ("jam", lambda i: not self.edges[i]))}

    @cached_property
    def infinite_k0(self):
        """Greatest subset of k=0 with a legal successor inside at every state.

        Peel all sinks and their newly stranded predecessors. On a finite
        graph each surviving state has a path to a cycle entirely in k=0.
        A stationary jam is not an infinite legal event word.
        """
        degree = {s: sum(self.kind[t] == 0 for _, t in row)
                  for s, row in enumerate(self.edges) if self.kind[s] == 0}
        queue = deque(s for s, k in degree.items() if k == 0)
        while queue:
            s = queue.popleft()
            del degree[s]
            for t in self.reverse[s]:
                if t in degree:
                    degree[t] -= 1
                    if degree[t] == 0:
                        queue.append(t)
        return frozenset(degree)

    def witness(self, parents, target):
        steps = []
        while parents[target] is not None:
            src, m = parents[target]
            steps.append({"before": state_record(self.states[src]), "center": m.center,
                          "old": sorted(m.old), "new": sorted(m.new),
                          "after": state_record(self.states[target])})
            target = src
        return {"distance": len(steps), "steps": steps[::-1]}

    def scc_profile(self, reachable):
        groups, owner, bottom = self.scc
        rows = Counter()
        for c in {owner[s] for s in reachable}:
            group = groups[c]
            counts = Counter(self.kind[s] for s in group)
            rows[bottom[c], tuple(counts[k] for k in range(3))] += 1
        return [{"terminal": terminal, "k012": counts, "components": multiplicity}
                for (terminal, counts), multiplicity in sorted(rows.items())]

    def active_long_sectors(self):
        """A pivot stays in one connected component of the long-bond graph.

        An even ring has two such components; there is no intrinsic name for
        either. Check conservation with a consistent temporary indexing, then
        discard that indexing in the displayed census.
        """
        at = {v: set() for v in self.graph}
        for bond in self.ports.motifs:
            a, b = bond
            at[a].add(b)
            at[b].add(a)
        unseen, classes = set(at), []
        while unseen:
            queue = [unseen.pop()]
            sites = set(queue)
            while queue:
                new = at[queue.pop()] & unseen
                unseen -= new
                sites |= new
                queue.extend(new)
            classes.append(frozenset(e for e in self.ports.motifs if e <= sites))
        rows = []
        for group in self.scc[0]:
            if not self.edges[group[0]]:
                continue
            occupants = {tuple(len(self.states[i] & c) for c in classes) for i in group}
            need(len(occupants) == 1, "long-bond component counts changed")
            counts, = occupants
            rows.append({"states": len(group), "long_counts_unordered": tuple(sorted(counts))})
        return sorted(rows, key=lambda r: (r["long_counts_unordered"], r["states"]))

    def census(self):
        jam = [i for i, row in enumerate(self.edges) if not row]
        need(all(not self.reverse[i] for i in jam), "reachable jam in this shell")
        active0 = [i for i, k in enumerate(self.kind) if k == 0 and self.edges[i]]
        ranks = self.return_ranks
        need(all(ranks["unique"][i] >= 1 and ranks["jam"][i] == -1 for i in active0),
             "active loss cannot recover or can reach jam")
        return {"n": self.n, "k012": self.counts, "strict_extra_raw_moves_k12": self.mismatches,
                "degree_histograms_by_k": self.degree, "isolated_jams": len(jam),
                "max_active_k0_min_to_unique": max((ranks["unique"][i] for i in active0),
                                                   default=None),
                "whole_shell_sccs": self.scc_profile(range(len(self.states))),
                "active_scc_long_components": self.active_long_sectors()}

    def preparation(self, i, h):
        state = fixture(self.n, 0, 1)[0] | fixture(self.n, i, h)[0]
        start = self.index[state]
        need(self.kind[start] == 1, "requires uniquely pairable preparation")
        parents, dist = bfs(self.edges, start)
        # BFS insertion order gives the first shortest witness; also account
        # for EVERY endpoint in its layer, independently of display tie-break.
        first = next(s for s in dist if self.kind[s] == 0)
        layer = [s for s in dist if dist[s] == dist[first] and self.kind[s] == 0]
        ranks = self.return_ranks
        recover = {}
        for key, d in ranks.items():
            s = first
            if d[s] < 0:
                recover[key] = None
                continue
            path = {s: None}
            while d[s]:
                m, t = next((m, t) for m, t in self.edges[s] if d[t] == d[s] - 1)
                path[t] = (s, m)
                s = t
            recover[key] = self.witness(path, s)
        rank_histogram = Counter(tuple(d[s] for d in ranks.values()) for s in layer)
        return {"preparation": [i, h], "first_loss": self.witness(parents, first),
                "nearest_loss_states": len(layer), "return_from_displayed_loss": recover,
                "nearest_loss_with_infinite_k0_path": sum(s in self.infinite_k0 for s in layer),
                "nearest_loss_ranks": [{"to_pairable_unique_jam": rank, "states": count}
                                       for rank, count in sorted(rank_histogram.items())],
                "reachable_states": len(dist), "reachable_sccs": self.scc_profile(dist)}


def report():
    shells = [Shell(11), Shell(16)]
    return {"scope": "finite active-gait matching readout, not particle statistics",
            "census": [dict(s.census(), relabeling_states=s.check_relabeling()) for s in shells],
            "preparations_n16": [shells[-1].preparation(i, h) for i, h in ((8, 1), (8, -1), (5, 1))],
            "ranks": "minimum atomic-event counts; -1 or null means unreachable, not improbable",
            "boundary": "Raw events preserve two short and two long bonds, not a number of "
                        "identifiable particles. A double reading does not select an identity; "
                        "two snapshots do not track particle identity or an exchange phase. A zero "
                        "reading is absence of this free-gait decomposition, not annihilation. "
                        "No simultaneous traffic, merging, exchange phase, Pauli rule, bosonic "
                        "enhancement, probability law or QM derivation is supplied by this test."}


if __name__ == "__main__":
    print(json.dumps(report(), indent=2))
