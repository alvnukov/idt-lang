"""Finite reduction of the native 000 <-> 111 offer to pair differences.

Only the given triples and their overlapping pairs enter the evolution. A bit
on a pair records whether the endpoints differ. Zero XOR on every cycle is
equivalent to liftability to vertex bits: integrate along a spanning tree,
then each remaining edge is checked by its fundamental cycle. On a connected
support the two choices at the tree root give complementary lifts. Dropping
global liftability but keeping the XOR checks on offered triples defines a
different, independent-link model, not a new interpretation of ordinary equals.

Run: python3 -m scripts.probe_relational_unanimous_clock [--json]
"""

import argparse
import json
from collections import Counter
from itertools import combinations

from scripts.probe_binary_unanimous_triples import offer as raw_offer

# Incidence list only; point numbers carry no geometry or dynamics.
FANO = ((0, 1, 2), (0, 3, 4), (0, 5, 6), (1, 3, 5),
        (1, 4, 6), (2, 3, 6), (2, 4, 5))


def span(generators):
    """GF(2) linear span, by successive independent additions."""
    space = {0}
    for g in generators:
        if g not in space:
            space.update([v ^ g for v in space])
    return space


class Relations:
    """Bit masks are edge sets. Only enabled() and offer() implement the rule."""

    def __init__(self, n, triples):
        self.n = n
        self.triples = tuple(tuple(sorted(t)) for t in triples)
        if (n < 0 or len(set(self.triples)) != len(self.triples)
                or any(len(t) != 3 or len(set(t)) != 3 or t[0] < 0 or t[2] >= n
                       for t in self.triples)):
            raise ValueError("expected distinct unordered triples on the given vertices")
        self.edges = tuple(sorted({e for t in self.triples for e in combinations(t, 2)}))
        self.bits = {e: 1 << i for i, e in enumerate(self.edges)}
        self.internal = tuple(sum(self.bits[e] for e in combinations(t, 2)) for t in self.triples)
        self.cuts = tuple(sum(b for (u, v), b in self.bits.items() if (u in t) != (v in t))
                          for t in self.triples)

    def enabled(self, d, line):
        return not (d & self.internal[line])

    def offer(self, d, line):
        return d ^ self.cuts[line] if self.enabled(d, line) else d

    def gradient(self, raw):
        """External audit only: pairwise XORs of a supplied vertex assignment."""
        return sum(b for (u, v), b in self.bits.items() if ((raw >> u) ^ (raw >> v)) & 1)

    def local_states(self):
        """Join the four even diagrams on each triple, enforcing shared links."""
        drawn, states = 0, [0]
        for t, mask in zip(self.triples, self.internal):
            a, b, c = (self.bits[e] for e in combinations(t, 2))
            options = (0, a | b, a | c, b | c)
            overlap = drawn & mask
            states = [s | q for s in states for q in options if not ((s ^ q) & overlap)]
            drawn |= mask
        return states


def components(adjacency):
    """Connected components; offers are involutions (internal tests survive cuts)."""
    unseen = set(adjacency)
    while unseen:
        root = unseen.pop()
        group, frontier = {root}, [root]
        while frontier:
            for dest in adjacency[frontier.pop()]:
                if dest in unseen:
                    unseen.remove(dest)
                    group.add(dest)
                    frontier.append(dest)
        yield frozenset(group)


def shape(group, adj):
    degrees = sorted(len(adj[d]) for d in group)
    if degrees == [2] * len(group):
        return f"C{len(group)}"
    if degrees == [1] * (len(group) - 1) + [len(group) - 1]:
        return f"K1,{len(group) - 1}"
    return "other"


def clock_audit(model, globally_liftable, adjacency, ready):
    """Compare to the original raw dynamics, including the quotient's odd cycles."""
    raw_masks = [sum(1 << v for v in t) for t in model.triples]
    raw_adj = {s: tuple(raw_offer(s, m) for m in raw_masks if raw_offer(s, m) != s)
               for s in range(1 << model.n)}
    global_adj = {d: adjacency[d] for d in globally_liftable}
    groups = list(components(global_adj))
    group_of = {d: g for g in groups for d in g}
    shapes, folded, points = Counter(), Counter(), Counter()
    fixed, odd_cycles, changing_readiness = 0, 0, 0
    for g in components(raw_adj):
        image = frozenset(model.gradient(s) for s in g)
        assert group_of[next(iter(image))] == image
        folded[f"{shape(g, raw_adj)}->{shape(image, global_adj)}"] += 1
        fixed += {((1 << model.n) - 1) ^ s for s in g} == g

    ref_firings = []
    for g in groups:
        kind = shape(g, global_adj)
        shapes[kind] += 1
        if kind != "C3":
            continue
        odd_cycles += 1
        offered = set.union(*(set(ready[d]) for d in g))
        point, = set.intersection(*(set(model.triples[i]) for i in offered))
        points[point] += len(g)
        # Each of the three distinct event labels fires on one undirected edge.
        for v in range(model.n):
            if v != point:
                link = model.bits[tuple(sorted((v, point)))]
                ref_firings.append(sum(bool(model.cuts[i] & link) for i in offered))
        # Choose a second native offer: its readiness differs across each firing.
        # This does not supply a stored observation of that readiness.
        changing_readiness += sum(set(ready[d]) != set(ready[e]) for d in g for e in global_adj[d])
    isolated = Relations(3, ((0, 1, 2),))
    return {
        "global_shapes": dict(shapes), "raw_shape_to_quotient": dict(folded),
        "raw_components_fixed_by_complement": fixed,
        "clock_states_by_persistent_vertex": dict(sorted(points.items())),
        "all_clock_events_changing_readiness": changing_readiness,
        "triangles_with_no_snapshot_binary_phase": odd_cycles,
        "least_greatest_firings_seen_by_fixed_clock_reference": (min(ref_firings), max(ref_firings)),
        "isolated_triangle": {"enabled": isolated.enabled(0, 0), "unchanged": isolated.offer(0, 0) == 0},
    }


def minimal_control():
    """Three triples and five used sites are both necessary for this type of jam.

    At most two triangles meet in an edge, one point or nothing: they span all
    cycles of their union. On <=4 vertices the finite family census is tested.
    """
    model = Relations(5, ((0, 1, 2), (0, 1, 3), (2, 3, 4)))
    unequal = ((0, 2), (1, 2), (0, 3), (1, 3), (2, 3), (2, 4))
    jam = sum(model.bits[e] for e in unequal)
    control = model.gradient((1 << 2) | (1 << 3))

    def direct_via(d):
        def bit(e):
            return int(bool(d & model.bits[e]))

        return bit((2, 3)), bit((0, 2)) ^ bit((0, 3))

    return {
        "triples": model.triples, "unequal_pairs": unequal,
        "local_but_no_lift": jam in model.local_states() and
        jam not in {model.gradient(s) for s in range(32)},
        "direct_vs_via_zero": direct_via(jam),
        "liftable_control_direct_vs_via_zero": direct_via(control),
        "both_jammed": all(not model.enabled(d, i) for d in (jam, control) for i in range(3)),
    }


def overlap_control():
    """An enabled ternary offer changes a neighboring offer's readiness."""
    model = Relations(4, ((0, 1, 2), (1, 2, 3)))
    initial = model.bits[1, 3] | model.bits[2, 3]
    after = model.offer(initial, 0)
    return {
        "triples": model.triples, "initial_unequal_pairs": ((1, 3), (2, 3)),
        "reference_offer_stutters_before_first": model.offer(initial, 1) == initial,
        "reference_offer_changes_state_after_first": model.offer(after, 1) != after,
        "first_offer_changes_only_links_to_reference": initial ^ after == initial,
    }


def verify():
    model = Relations(7, FANO)
    local = model.local_states()
    gradients = {model.gradient(s) for s in range(1 << model.n)}
    # All vertex cuts classify possible cycle XOR values, not dynamics or gauge
    # equivalences of the guard: a single-site flip can change which lines fire.
    sector = {}
    for d in local:
        if d not in sector:
            orbit = {d ^ g for g in gradients}
            representative = min(orbit)
            sector.update(dict.fromkeys(orbit, representative))
    assert sector.keys() == set(local)
    ready = {d: tuple(i for i in range(len(FANO)) if model.enabled(d, i)) for d in local}
    adj = {d: tuple(model.offer(d, i) for i in ready[d]) for d in local}
    jams = Counter({tag: 0 for tag in sector.values()})
    for d in local:
        jams[sector[d]] += not ready[d]
    move_span = span(model.cuts)
    cycle_rank = len(model.edges) - model.n + 1
    local_rank = len(span(model.internal)).bit_length() - 1
    return {
        "fano": {
            "links": len(model.edges),
            "cycle_rank": cycle_rank, "local_check_rank": local_rank,
            "extra_cycle_checks_for_global_lift": cycle_rank - local_rank,
            "local_states": len(local), "gradient_states": len(gradients),
            "sector_size_histogram": dict(Counter(Counter(sector.values()).values())),
            "jam_counts_per_sector": dict(sorted(Counter(jams.values()).items())),
            "only_gradient_sector_jam_free": {s for s, j in jams.items() if not j} == {sector[0]},
            "component_sizes": dict(sorted(Counter(map(len, components(adj))).items())),
            "line_cut_span_rank": len(move_span).bit_length() - 1,
            "unconditional_move_packets": len(local) // len(move_span),
            "every_transition_preserves_holonomy": all(sector[s] == sector[e] for s in local for e in adj[s]),
            "active_states": sum(bool(ready[d]) for d in local),
            "active_moves_have_enabled_inverse": all(
                model.enabled(e, i) and model.offer(e, i) == d
                for d in local for i, e in zip(ready[d], adj[d])),
            "links_toggled_per_enabled_move": sorted({(d ^ e).bit_count() for d in local for e in adj[d]}),
        },
        "clock": clock_audit(model, gradients, adj, ready),
        "minimal_control": minimal_control(),
        "overlap_control": overlap_control(),
        "boundary": "Finite comparison on supplied incidence, not a forced clock or geometry. "
                    "Raw Fano no-jam survives quotient by uniform complement, but not replacement "
                    "of globally integrable differences by all locally even transports. "
                    "Zero holonomy can be imposed directly without choosing absolute shades. "
                    "Native offer readiness and external link/path comparisons are not a built "
                    "detector, travelling signal, duration, or spatial reconstruction.",
    }


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--json", action="store_true")
    args = parser.parse_args()
    result = verify()
    if args.json:
        print(json.dumps(result, indent=2))
    else:
        print("Fano jam count -> number of sectors:", result["fano"]["jam_counts_per_sector"])
        print("Globally liftable quotient:", result["clock"]["global_shapes"])
        print("Minimal nonliftable jam:", result["minimal_control"])
        print(result["boundary"])
