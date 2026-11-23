"""Known edge-reversal scheduling for Rule 54 on a supplied cycle.

Add one prepared arrow per neighboring pair of payload sites. A site may
update only when both arrows point into it, then reverses those arrows.
Indices and arrow bits label the supplied graph; they are not scheduling
addresses. The staggered reference is compared only at matching causal cuts.
The extra arrows, graph and local rule are inputs, not derived from raw
contacts. This does not construct spatial geometry, physical or quantum time.

Run: python3 -m scripts.probe_binary_sink_clock
"""

from __future__ import annotations

import json
from functools import cache
from itertools import combinations

from scripts.probe_binary_cycle_solitons import Cycle


def _require(condition: bool, message: str) -> None:
    if not condition:
        raise ArithmeticError(message)


def _is_sink(n: int, arrows: int, site: int) -> bool:
    # Bit i means edge i points i -> i+1, with indices modulo n.
    return bool(arrows >> ((site - 1) % n) & 1 and not (arrows >> site & 1))


def ready_sites(n: int, arrows: int) -> tuple[int, ...]:
    return tuple(site for site in range(n) if _is_sink(n, arrows, site))


def even_sink_arrows(n: int) -> int:
    if n < 4 or n % 2:
        raise ValueError("the staggered reference needs an even cycle of length at least 4")
    return sum(1 << i for i in range(1, n, 2))


def _reverse_at_sink(n: int, arrows: int, site: int) -> int:
    if not 0 <= site < n or not _is_sink(n, arrows, site):
        raise ValueError(f"site {site} is not a sink")
    return arrows ^ ((1 << ((site - 1) % n)) | (1 << site))


def _update_payload(n: int, payload: int, site: int) -> int:
    neighbors = (1 << ((site - 1) % n)) | (1 << ((site + 1) % n))
    return payload ^ (1 << site) if payload & neighbors else payload


def fire(n: int, arrows: int, payload: int, site: int) -> tuple[int, int]:
    return _reverse_at_sink(n, arrows, site), _update_payload(n, payload, site)


def cut_inventory(n: int) -> dict:
    """Explore every reachable cut with local counts at most two, plus every join.

    Each representative map gives the current payload for every initial bit
    mask. Compare it with every incoming path before merging; no path is
    discarded on the grounds that it has the same control state alone.
    """
    initial = even_sink_arrows(n), (0,) * n
    complete_counts = (2,) * n
    identity = tuple(range(1 << n))
    maps = {initial: identity}
    pending = [initial]
    terminals = []
    transitions = joins = ready_pairs = 0

    while pending:
        arrows, counts = cut = pending.pop()
        payload_map = maps[cut]
        sites = tuple(site for site in ready_sites(n, arrows) if counts[site] < 2)
        if not sites:
            _require(counts == complete_counts, f"premature capped terminal at {cut}")
            terminals.append(cut)

        after_one = {}
        for site in sites:
            target_arrows = _reverse_at_sink(n, arrows, site)
            target_counts = counts[:site] + (counts[site] + 1,) + counts[site + 1:]
            after = tuple(_update_payload(n, payload, site) for payload in payload_map)
            target = target_arrows, target_counts
            transitions += 1
            after_one[site] = target_arrows, after
            if target in maps:
                joins += 1
                _require(maps[target] == after, f"different payload maps at cut {target}")
            else:
                maps[target] = after
                pending.append(target)

        for left, right in combinations(sites, 2):
            # Simultaneous sinks are nonadjacent: neither changes what the
            # other reads or its right to fire. Check both orders anyway.
            left_arrows, left_map = after_one[left]
            right_arrows, right_map = after_one[right]
            lr = _reverse_at_sink(n, left_arrows, right)
            rl = _reverse_at_sink(n, right_arrows, left)
            _require(lr == rl, f"control diamond failed at {cut}: {left}, {right}")
            _require(
                all(_update_payload(n, a, right) == _update_payload(n, b, left)
                    for a, b in zip(left_map, right_map, strict=True)),
                f"payload diamond failed at {cut}: {left}, {right}",
            )
            ready_pairs += 1

    complete = initial[0], complete_counts
    _require(terminals == [complete], f"unexpected terminal cuts: {terminals}")
    reference = Cycle(n)
    expected = identity
    for phase in (0, 1, 0, 1):
        expected = tuple(reference.half_step(payload, phase) for payload in expected)
    _require(maps[complete] == expected, f"two-sweep disagreement for n={n}")
    return {
        "n": n,
        "cuts": len(maps),
        "transitions": transitions,
        "joining_transitions": joins,
        "ready_pairs": ready_pairs,
        "payloads_per_cut": len(identity),
        "terminal_cuts": len(terminals),
        "complete_arrows": complete[0],
        "complete_counts": complete[1],
        "complete_payload_map": maps[complete],
    }


def unguarded_control() -> dict[str, int]:
    n, initial = 6, 1
    report = {"n": n, "initial_payload": initial}
    for name, order in (
        ("ascending", range(n)),
        ("reverse", reversed(range(n))),
        ("even_odd", (*range(0, n, 2), *range(1, n, 2))),
    ):
        payload = initial
        for site in order:
            payload = _update_payload(n, payload, site)
        report[name] = payload
    return report


def periodic_height(n: int, arrows: int) -> tuple[int, ...] | None:
    """Construct a ±1 height slice normalized at site zero, if it closes."""
    vertices = [0]
    for edge in range(n):
        vertices.append(vertices[-1] + (1 if arrows >> edge & 1 else -1))
    return tuple(vertices[:-1]) if vertices[-1] == 0 else None


def orientation_inventory(n: int) -> dict:
    """Exhaust all arrow orientations and legal one-site control transitions.

    Reversal preserves the clockwise arrow count k. On an even cycle a
    regular alternating orientation has k=n/2, so an active tilted cycle
    cannot reach it. Tilt alone is not a deadlock or a physical exclusion.
    """
    if n < 3:
        raise ValueError("need a simple cycle of length at least 3")
    full = (1 << n) - 1
    deadlocks = []
    slices = tilted = 0
    successors = {}
    for arrows in range(full + 1):
        clockwise = arrows.bit_count()
        balanced = 2 * clockwise == n
        height = periodic_height(n, arrows)
        _require((height is not None) == balanced, f"incorrect height closure at {arrows}")
        if height is not None:
            slices += 1
            _require(all(height[(i + 1) % n] - height[i] == (1 if arrows >> i & 1 else -1)
                         for i in range(n)), f"height does not encode {arrows}")
        sites = ready_sites(n, arrows)
        if not sites:
            deadlocks.append(arrows)
        elif not balanced:
            tilted += 1
        after = []
        for site in sites:
            target = _reverse_at_sink(n, arrows, site)
            _require(target.bit_count() == clockwise, f"tilt changed at {(arrows, site)}")
            _require(target not in (0, full), f"active orientation became cyclic at {arrows}")
            # Reversal makes these two incident edges both outgoing. Neither
            # can return to incoming until its other endpoint fires.
            _require(
                not (target >> ((site - 1) % n) & 1) and bool(target >> site & 1),
                f"incident edges not both outgoing after {(arrows, site)}",
            )
            after.append((site, target))
        successors[arrows] = tuple(after)
    _require(deadlocks == [0, full], f"wrong deadlocks on length {n}: {deadlocks}")

    @cache
    def gap(arrows: int) -> int:
        # Orientations cannot recur while 0 is held fixed. A recurrence would
        # require equal endpoint firing counts along every edge, hence all
        # counts zero by connectedness and the count at 0 being zero.
        return max((1 + gap(target) for site, target in successors[arrows] if site != 0),
                   default=0)

    max_gap = max(map(gap, successors))
    _require(max_gap <= n * n // 4, f"event-gap bound failed on length {n}")
    return {
        "n": n,
        "orientations": full + 1,
        "deadlocks": tuple(deadlocks),
        "active_orientations": full + 1 - len(deadlocks),
        "periodic_height_slices": slices,
        "active_tilted_orientations": tilted,
        "transitions": sum(map(len, successors.values())),
        # Rotation of the all-orientation inventory makes the choice v=0 WLOG.
        "max_v_free_events": max_gap,
    }


def sharp_gap(n: int) -> dict:
    """Replay a sharp even-cycle gap, starting immediately after zero fires.

    Firings at an edge's endpoints alternate: only the other endpoint can
    return the edge to the orientation needed to fire there a second time.
    Over any interval the two counts differ by at most one. If v never fires,
    the count at j is at most dist(v,j), hence at most floor(n²/4) events in
    total. An active cycle always has a sink, so continued event selection
    cannot starve any site forever. This bounds event count, not elapsed time.
    """
    if n < 4 or n % 2:
        raise ValueError("this sharp witness uses an even cycle of length at least 4")
    initial = (1 << (n // 2)) - 1  # Two paths oriented from zero to its antipode.
    before = initial ^ (1 | (1 << (n - 1)))
    arrows = _reverse_at_sink(n, before, 0)
    _require(arrows == initial, "initial sharp-gap orientation must follow a zero firing")
    counts = [0] * n
    order = []
    distances = tuple(min(i, n - i) for i in range(n))
    bound = sum(distances)
    while (sites := tuple(i for i in ready_sites(n, arrows) if i != 0)):
        site = sites[0]  # A deterministic replay witness, not part of the guard.
        arrows = _reverse_at_sink(n, arrows, site)
        counts[site] += 1
        order.append(site)
        _require(counts[site] <= distances[site], f"distance bound failed at {site}")
    _require(tuple(counts) == distances and len(order) == bound == n * n // 4,
             f"sharp-gap witness did not attain the bound for n={n}")
    _require(ready_sites(n, arrows) == (0,), "sharp gap did not end with zero ready")
    return {
        "n": n,
        "before_zero_fire": before,
        "after_zero_fire": initial,
        "zero_free_order": tuple(order),
        "counts": tuple(counts),
        "events": len(order),
    }


def probe() -> dict:
    cuts = []
    for n, expected in ((4, (16, 4)), (6, (66, 33)), (8, (264, 200))):
        row = cut_inventory(n)
        _require((row["transitions"], row["ready_pairs"]) == expected,
                 f"bounded graph coverage changed at n={n}")
        cuts.append({key: value for key, value in row.items() if key != "complete_payload_map"})
    unguarded = unguarded_control()
    _require((unguarded["ascending"], unguarded["reverse"], unguarded["even_odd"]) == (63, 62, 35),
             "unguarded order control changed")
    return {
        "bounded_cuts": cuts,
        "unguarded_orders": unguarded,
        "orientation_inventory": [orientation_inventory(n) for n in range(3, 9)],
        "sharp_gaps": [sharp_gap(n) for n in range(4, 17, 2)],
    }


if __name__ == "__main__":
    print(json.dumps(probe(), indent=2))
