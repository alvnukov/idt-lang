"""Fairness and first passage on one fixed rule-32 raw cube packet.

Run: python3 -m scripts.probe_packet_scheduler_fairness

The externally prepared source, target, proposal words and random sampling
laws are inputs. An offer to a disabled center leaves the raw word fixed.
First contact (target rung absent) differs from reaching the target singleton.
All counts concern this finite graph: no intrinsic scheduler, physical clock,
observer, spatial dimension or Born law is inferred.
"""

from __future__ import annotations

import json
from collections import Counter
from fractions import Fraction
from itertools import permutations
from math import factorial

from scripts.probe_facilitated_forest_signal import (
    Incidence, Moves, carriers, distances, edge, indices, lift, need,
)
from scripts.probe_localized_shell_packets import RawShell, decode


def closed_tour(rows: Moves, start: int, allowed: set[int]) -> tuple[int, ...]:
    """Traverse each internal unordered event once out and once back."""
    visited_edges = set()
    centers = []

    def walk(state):
        for center, target in sorted(rows[state].items()):
            event = edge(state, target)
            if target not in allowed or event in visited_edges:
                continue
            visited_edges.add(event)
            centers.append(center)
            walk(target)
            need(rows[target].get(center) == state, "missing inverse center")
            centers.append(center)

    walk(start)
    return tuple(centers)


def replay(rows, supports, start, target, target_rung, centers):
    state = start
    states = {start}
    taken = set()
    for center in centers:
        if center in rows[state]:
            taken.add((state, center))
            state = rows[state][center]
        states.add(state)
    enabled = {(w, v) for w in states for v in rows[w]}
    return {
        "centers": centers,
        "closed": state == start,
        "supports": tuple(sorted(tuple(sorted(supports[w])) for w in states)),
        "enabled_labels": tuple(sorted({v for _, v in enabled})),
        "fired_labels": tuple(sorted({v for _, v in taken})),
        "taken_state_actions": len(taken),
        "missed_state_actions": len(enabled - taken),
        "target_contact": any(not (w & target_rung) for w in states),
        "target_singleton": target in states,
    }


def sweep_census(rows, supports, start, target, upper):
    """Repeat each permutation until boundary return; count after EVERY offer."""
    words = tuple(rows)
    ids = {w: i for i, w in enumerate(words)}
    marks = tuple(1 << i for i in range(len(words)))
    singleton = sum(marks[ids[w]] for w in rows if len(supports[w]) == 1)
    root = ids[start]
    sink = marks[ids[target]]
    table = tuple(tuple(ids[rows[w].get(v, w)] for w in words) for v in upper)
    # Each center acts by an involution including its no-op rows. Thus each
    # sweep permutes the raw words and returns to root in at most len(words).
    for action in table:
        need(all(action[action[i]] == i for i in range(len(words))), "bad center map")
    counts = Counter()
    hits = 0
    for order in permutations(table):
        state = root
        seen = marks[root]
        for _ in words:
            for action in order:
                state = action[state]
                seen |= marks[state]
            if state == root:
                break
        else:
            raise ArithmeticError("permutation sweep failed to return")
        counts[(seen & singleton).bit_count(), seen.bit_count()] += 1
        hits += bool(seen & sink)
    need(sum(counts.values()) == factorial(len(upper)), "incomplete order census")
    return {
        "orders": sum(counts.values()),
        "hit_target": hits,
        "histogram_singletons_raw_orders": tuple((*k, n) for k, n in sorted(counts.items())),
    }


def check_conjugacy(raw, rows, supports, background):
    """Mix the layers, reorder ports, and transport EVERY state-center action.

    Since the full table, idle steps and support decoding commute, transporting
    a schedule (including its source/target and labels) preserves its census.
    """
    n = len(raw.stars) // 2
    image = tuple(2 * v + 1 for v in reversed(range(n))) + tuple(2 * v for v in range(n))
    renamed_edges = tuple(edge(image[u], image[v]) for u, v in raw.edge_bits)
    renamed = Incidence.from_edges(2 * n, renamed_edges, 4)
    bits = tuple(renamed.edge_bits[e] for e in renamed_edges)
    shell = RawShell(renamed)

    def transport(w):
        return sum(bits[i] for i in indices(w))

    for w, row in rows.items():
        renamed_word = transport(w)
        renamed_row = shell.offers(renamed_word, 32)
        need(decode(renamed, renamed_word) == (
            frozenset(image[v] for v in supports[w]), transport(background)
        ), "relabeling changed decoded support")
        for v in range(2 * n):
            need(renamed_row.get(image[v], renamed_word) == transport(row.get(v, w)),
                 "relabeling changed a firing or idle offer")
    return len(rows) * 2 * n


def mean_first_hits(rows: Moves, target: int, center_count: int | None):
    """Solve the finite absorbing-target Bellman equations in exact rationals.

    Active-uniform: independent draws uniform *conditional on the state*,
    not IID fired center labels. Raw-uniform: IID uniform over all centers,
    with disabled proposals paid for as steps. Cancelling idle self-loops
    leaves the same graph Laplacian with different right-hand sides.
    """
    words = tuple(w for w in rows if w != target)
    ids = {w: i for i, w in enumerate(words)}
    n = len(words)
    a = [[Fraction(0) for _ in range(n + 1)] for _ in words]
    for i, w in enumerate(words):
        a[i][i] = Fraction(len(rows[w]))
        for t in rows[w].values():
            if t != target:
                a[i][ids[t]] -= 1
        a[i][-1] = Fraction(len(rows[w]) if center_count is None else center_count)
    for j in range(n):
        pivot = next((i for i in range(j, n) if a[i][j]), None)
        need(pivot is not None, "singular first-passage system")
        a[j], a[pivot] = a[pivot], a[j]
        a[j] = [v / a[j][j] for v in a[j]]
        for i in range(n):
            if i != j and a[i][j]:
                factor = a[i][j]
                a[i] = [v - factor * u for v, u in zip(a[i], a[j])]
    means = {w: a[i][-1] for i, w in enumerate(words)}
    means[target] = Fraction(0)
    # Independently evaluate the unmodified Markov equations, including idles.
    for w in words:
        row = rows[w]
        successors = (tuple(row.values()) if center_count is None else
                      tuple(row.get(v, w) for v in range(center_count)))
        need(means[w] == 1 + sum(means[t] for t in successors) / len(successors),
             "nonzero exact Bellman residual")
    return means


def scheduler_fairness():
    raw, rungs = lift(carriers()["cube"])
    background = sum(rungs)
    start, target = (raw.prepare(background, [v]) for v in (0, 6))
    rows = RawShell(raw).orbit(start, 32)
    supports = {w: decode(raw, w)[0] for w in rows}
    upper = tuple(range(len(rungs)))
    all_centers = len(raw.stars)
    need((len(rows), len(set(supports.values()))) == (20, 20), "unexpected raw orbit")
    need({v for row in rows.values() for v in row} == set(upper), "non-idle lower center")
    need(all((6 in supports[w]) == (not (w & rungs[6])) for w in rows),
         "first-contact reader disagrees with raw rung")
    conjugate = check_conjugacy(raw, rows, supports, background)

    def tour(centers):
        return replay(rows, supports, start, target, rungs[6], centers)

    bounded = tour((*range(all_centers), 1))
    need(bounded["closed"] and bounded["supports"] == ((0,), (0, 1)),
         "bounded proposal counterexample failed")
    allowed = {w for w, s in supports.items() if
               (len(s) == 1 and s <= {0, 1}) or (len(s) == 2 and s & {0, 1})}
    local = tour(closed_tour(rows, start, allowed))
    need(len(allowed) == 7 and len(local["supports"]) == 7 and local["closed"]
         and local["fired_labels"] == local["enabled_labels"]
         and local["missed_state_actions"] > 0 and not local["target_contact"],
         "label-fair counterexample failed")
    full = tour(closed_tour(rows, start, set(rows)))
    need(full["closed"] and len(full["supports"]) == len(rows)
         and full["missed_state_actions"] == 0, "incomplete transition tour")

    path = distances({w: row.values() for w, row in rows.items()}, start)
    return {
        "scope": "Finite conditional scheduler comparison on a supplied raw rule-32 "
                 "cube packet. No intrinsic time, probability law or measured physics.",
        "bounded_proposals": bounded,
        "permutation_sweeps": sweep_census(rows, supports, start, target, upper),
        "conjugate_state_center_checks": conjugate,
        "label_fair": local,
        "state_transition_fair": full,
        "fairness_argument": "If every enabled action of every recurrent state fires "
            "infinitely often there, its successors recur too. The nonempty recurrent "
            "set is then closed and, by finite symmetric connectivity, is the whole "
            "orbit. No uniform deadline: repeat the closed target-avoiding word any "
            "finite number of times before switching forever to the full fair tour.",
        "opposite_singleton": {
            "shortest_enabled_events": path[target],
            "shortest_to_first_contact": min(d for w, d in path.items() if not w & rungs[6]),
            "mean_enabled_events": str(mean_first_hits(rows, target, None)[start]),
            "mean_all_center_proposals": str(mean_first_hits(rows, target, all_centers)[start]),
        },
    }


if __name__ == "__main__":
    print(json.dumps(scheduler_fairness(), sort_keys=True))
