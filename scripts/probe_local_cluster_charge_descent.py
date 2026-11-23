"""Does a sum of closed-quartet ballot values descend to anonymous packet soup?

Only the supplied C command is available here, on ANY chosen four packets.
Always distinguish (i) any isolated four-packet container, including idle
ones, (ii) a currently *firing* motif, (iii) a maximal disjoint packing of
such motifs, and (iv) components physically separated for the entire run.
Those are different prescriptions, not progressively stronger evidence
of actual particle charges. We test descent through forgetting the grouping:
one bare multiset and one reversible reachability orbit must have one value.

The eight-packet witness has unambiguous endpoint *counts* of active motifs
even without choosing a maximal-packing tie breaker. The only scalar on
these active-motif/singleton generators that escapes its arithmetic
obstruction assigns every single packet 3/4: then the sum is just 3N/4.
It does not agree with I_q on all isolated idle quartets. This does not
rule out new physics that supplies locality, association, or changes C.
"""

from __future__ import annotations

import json
import sys
from collections import Counter, deque
from itertools import combinations, combinations_with_replacement
from math import comb
from pathlib import Path

if not __package__:
    sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
from scripts.probe_anonymous_reference_collision import QUARTETS, canon, field_sum, step
from scripts.probe_blind_collision_charge import (
    INDEX,
    STATES,
    check_span,
    difference,
    need,
    occ,
)

Q = tuple(3*occ(x)[1]-2*occ(x)[0] for x in STATES)
MOVES = {a: b for a in QUARTETS if (b := step(a)) != a}
PATH = ((0, 9, 9, 9, 10, 30, 30, 30), (0, 5, 5, 9, 9, 9, 17, 30), (0, 9, 9, 17, 18, 30, 30, 30))


def embedded(state):
    """All inequivalent enabled motif+rest instances, forgetting packet order."""
    result = {}
    for p in combinations(range(len(state)), 4):
        a = tuple(state[i] for i in p)
        if a in MOVES and a not in result:
            rest = tuple(x for i, x in enumerate(state) if i not in p)
            result[a] = (rest, canon((*MOVES[a], *rest)))
    return result


def maximal_sizes(state):
    # Only invoked at N=8: a nonfiring four-element remainder consists of
    # four unmatched singles; a firing remainder must enter a maximal packing.
    need(len(state) == 8, "maximal-packing decoder restricted to eight")
    return sorted({1 + int(rest in MOVES) for rest, _ in embedded(state).values()} or {0})


def pack(xs):
    # Independent occupation-vector representation for the whole-graph census:
    # one four-bit count per record, never exceeding 8, so addition is union.
    return sum(1 << (4*INDEX[x]) for x in xs)


def census(n):
    parent = {}
    sizes = {}

    def root(x):
        while parent[x] != x:
            parent[x] = parent[parent[x]]
            x = parent[x]
        return x

    def join(x, y):
        for v in (x, y):
            if v not in parent:
                parent[v] = v
                sizes[v] = 1
        x, y = root(x), root(y)
        if x != y:
            if sizes[x] < sizes[y]:
                x, y = y, x
            parent[y] = x
            sizes[x] += sizes.pop(y)

    swaps = [(pack(a), pack(b)) for a, b in MOVES.items() if a < b]
    instances = 0
    for rem in combinations_with_replacement(STATES, n-4):
        base = pack(rem)
        for a, b in swaps:
            join(base + a, base + b)
            instances += 1
    total = comb(15+n, n)
    need(instances == len(swaps)*comb(15+n-4, n-4), "all embedded command instances")
    need(sum(sizes.values()) == len(parent), "invalid component census")
    return {"N": n, "states": total, "states_with_enabled_moves": len(parent),
            "idle_singletons": total-len(parent), "nontrivial_orbits": len(sizes),
            "largest_orbit": max(sizes.values()), "undirected_command_instances": instances,
            "witness_orbit_size": sizes[root(pack(PATH[0]))] if n == 8 else None}


def ungrouped_controls():
    # Singleton energy is constant under translations. If any closed quartet
    # (idle included) can be declared separate from an unbound single, these
    # two disjoint-support lifts of the SAME state already demand two values.
    x, y = (0, 0, 0, 9), (0, 0, 0, 3)
    need(canon((*x, 3)) == canon((*y, 9)) and 3 not in x and 9 not in y, "disjoint-support lifts")
    need((field_sum(x, Q), field_sum(y, Q)) == (3, -12), "idle/active ambiguity")
    # At n=4 the isolated value is well-defined for every multiset and C
    # preserves it. If additivity also applies to arbitrary singleton-only
    # decompositions, impossibility can arise already there; here a quartet
    # must actually be present in both tested decompositions.
    need(all(field_sum(a, Q) == field_sum(step(a), Q) for a in QUARTETS), "standalone quartet")
    need(len(MOVES) == 192 and {field_sum(a, Q) for a in MOVES} == {3}, "active motif values")
    double = {canon((*a, *b)) for a, b in combinations_with_replacement(MOVES, 2)}
    need(len(double) == 17016, "distinct two-active-motif input states")
    sizes = [maximal_sizes(s) for s in PATH]
    need(sizes == [[2], [1, 2], [1]], "consensus/ambiguous/consensus endpoints")
    enabled = [embedded(s) for s in PATH]
    need([len(t) for t in enabled] == [2, 4, 1], "endpoint uniqueness up to swapping two active clusters")
    start, end = enabled[0], enabled[-1]
    need(all(rest in start and not set(a) & set(rest) for a, (rest, _) in start.items()), "start mixture")
    ((only, (idle, _)),) = end.items()
    need(idle not in MOVES and not set(only) & set(idle) and field_sum(idle, Q) == 15, "separated idle remainder")
    steps = []
    for i, state in enumerate(PATH[:2]):
        instances = embedded(state)
        used, = (a for a, (_, target) in instances.items() if target == PATH[i+1])
        rest, _ = instances[used]
        steps.append({"before": state, "move": [used, MOVES[used]], "untouched": rest, "after": PATH[i+1]})
    need(PATH[0] in double and PATH[1] in double and PATH[2] not in double, "maximum packing loss")
    # The prior 4->8 obstruction requires counting two possible active motifs.
    # At 4<=N<8 every state enabling a move has exactly one motif in a
    # maximal packing, as does each neighbor (the reversal remains enabled).
    # One move cannot connect [2] directly to [1]: its complementary active
    # motif is still present even after the chosen motif reverses.
    orbit = {PATH[0]}
    todo = deque(orbit)
    counts = Counter()
    while todo:
        state = todo.popleft()
        kinds = maximal_sizes(state)
        counts[tuple(kinds)] += 1
        for _, nxt in embedded(state).values():
            if kinds == [2]:
                need(nxt in double, "an immediate jump from consensus two to one")
            if nxt not in orbit:
                orbit.add(nxt)
                todo.append(nxt)
    need(len(orbit) == 900 and PATH[2] in orbit, "reachable orbit count")
    return {"idle_quartet_allowed": {"same_five": canon((*x, 3)), "quartets": [x, y],
                                     "spectators": [3, 9], "quartet_values": [3, -12]},
            "two_active_only": {"distinct_eight_record_unions": len(double), "all_sums": [6]},
            "active_packing_wall": {"steps": steps, "all_maximal_packing_sizes": sizes,
                                    "orbit_counts_by_packing_sizes": {str(k): v for k, v in sorted(counts.items())},
                                    "enabled_subquartet_counts": list(map(len, enabled)),
                                    "idle_remainder_as_complete_quartet": {"active": only, "idle": idle,
                                        "start_sum": 6, "end_sum": field_sum(only, Q)+field_sum(idle, Q)},
                                    "singleton_value_equation": "6 = 3 + 4s, hence s = 3/4",
                                    "minimal_N_for_competing_active_counts": 8,
                                    "shortest_consensus_to_consensus_steps": 2}}


def extensive_controls():
    parity = tuple(occ(x)[1] % 2 for x in STATES)
    rows = {difference(a, b) for a, b in MOVES.items()}
    check_span(rows, [(1,)*16, parity])
    # Without translation-invariance, two per-packet parity populations
    # survive C. A common shift by a mixed record swaps these colors, so
    # requiring an absolute scalar on all configurations forces equal weights.
    need(all(parity[INDEX[x ^ 9]] == 1-parity[INDEX[x]] for x in STATES), "color interchange")
    a, b = (0, 0, 0, 9), (0, 9, 9, 9)

    def parity_value(state):
        colored = sum(parity[INDEX[v]] for v in state)
        return 3*min(colored, len(state)-colored)

    need(all(parity_value(a) == parity_value(b) == 3 for a, b in MOVES.items()), "minority color countermodel")
    need(parity_value(a)+parity_value(b) == 6 and parity_value((*a, *b)) == 12, "nonadditivity")

    def linear(state, origin):
        return sum(Q[INDEX[v ^ origin]] for v in state)

    after = MOVES[a]
    need([linear(s, 0) for s in (a, after)] == [1, 1]
         and [linear(s, 3) for s in (a, after)] == [-11, 1], "shared relative origin countermodel")
    # Anonymous chambers (an extra space of sites, with local co-presence),
    # capacity <=4; no permanent packet names or prescribed quartets. Only
    # within-cell C, whole-cell translations and cell permutations are allowed.
    # A sum of within-cell pair values is then exact for ANY number of cells:
    # one term changes per C command and that term was exhausted above.
    # Opening a wall to free single-packet transport invalidates the argument.
    sealed = [field_sum(a, Q), field_sum(after, Q)]
    transferred = field_sum((0, 0, 0), Q) + field_sum((9,), Q)
    need(sealed == [3, 3] and transferred == 0, "chamber leakage")
    return {"translation_invariant_packet_additive_space": "only constants times N",
            "nonadditive_invariant": {"formula": "3 min(n_even,n_odd) for marked-block occupation parity",
                                      "isolated_active_values": [3, 3], "union_value": 12},
            "shared_external_origin": {"origin_0": [1, 1], "origin_3": [-11, 1]},
            "local_chamber_extension": {"allowed": "capacity <=4; within-cell C, rigid translations and relabeling",
                                        "extra_input": "local site co-presence/physical isolation, not permanent packet IDs",
                                        "sealed_charge": sealed, "after_single_packet_leak": transferred}}


def probe():
    controls = ungrouped_controls()
    graphs = [census(n) for n in range(5, 9)]
    need(graphs[-1]["witness_orbit_size"] == 900, "independent occupation-vector census")
    return {"status": "finite_named_record_grammar_not_physical_charge", "decomposition": controls,
            "whole_graph": graphs, "countermodels": extensive_controls()}


if __name__ == "__main__":
    print(json.dumps(probe(), sort_keys=True))
