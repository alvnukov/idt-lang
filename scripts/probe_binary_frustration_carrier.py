"""Equal-neighbour binary frustration on folded five, and ensemble controls.

The only energy is the count B of edges whose two spins agree. Since
B=20+s^T A s/4 and the minimum adjacency eigenvalue is -3, B>=8.
In the 5D lowest eigenspace the single-port characters chi_i span.
Their ten pair products are distinct nonconstant characters, so if
s=sum a_i chi_i then s²=1 forces a_i a_j=0 for i!=j and sum a_i²=1.
The ten states +/-chi_i are precisely the binary ground states.

Choose the ground ensemble uniformly (globally flipped signs give the
same relational readings). For a nonadjacent ordered pair (r,t), let
X=s_r*s_t, Y=s_r*s_v. The connected binary correlation is computed
directly, before comparing a separate Dirichlet projector. A single
fixed ground configuration has no covariance. The graph/matching
energy alone is not a law for ensemble preparation and the result is
not a hopping charge, gauge interaction, or physical identification.

A specified stochastic update rule does give an unconditioned route
to this ensemble: propose all single spins and adjacent pairs with
equal positive probability, accepting strict single-spin improvements
and energy-neutral simultaneous edge-pair flips. Every non-ground
state has an allowed path to an absorbing ground by the finite trap
census. Finite-state absorption and an invariant initial distribution
then give uniform ground orientations in the infinite-time limit.
Neither the coordinated pair update, symmetric scheduler nor a finite
completion time follows from the energy alone.

For any positive Gibbs parameter x, exact proportionality of the
whole connected profile to its ground version would force G2=1/5
by the mark/neither ratio and then G1=-3/5 by the both/neither ratio.
The latter fixes the mean energy at 8, impossible with positive
weight on every state above the minimum.
"""

from __future__ import annotations

import json
from collections import Counter, deque
from fractions import Fraction
from itertools import combinations

N = 16
ALL = (1 << N) - 1
SPINS = range(ALL+1)
Matrix = tuple[tuple[int, ...], ...]
Graph = tuple[frozenset[int], ...]


def need(condition, why):
    if not condition:
        raise ArithmeticError(why)


def folded_fixture() -> tuple[Graph, tuple[int, ...]]:
    even = tuple(v for v in range(32) if v.bit_count() % 2 == 0)
    # Renumber the fixture before the energy/ensemble computations.
    words = tuple(even[(5*i+7) % N] for i in range(N))
    graph = tuple(frozenset(j for j, v in enumerate(words) if (u ^ v).bit_count() == 4) for u in words)
    return graph, words


def site_pair(mask: int, a: int, b: int) -> int:
    return 1-2*((mask >> a ^ mask >> b) & 1)


def spectra_certificate(graph: Graph) -> tuple[tuple[int, int], ...]:
    need(len(graph) == N and all(len(row) == 5 for row in graph), "wrong folded vertex or degree count")
    need(all(len(x & y) == 3*int(i == j)+2-2*int(j in x)
             and (j in x) == (i in y)
             for i, x in enumerate(graph) for j, y in enumerate(graph)), "folded adjacency polynomial A²")
    edges = tuple((u, v) for u, row in enumerate(graph) for v in row if u < v)
    need(len(edges) == 40, "edge count")
    # A²=3I-2A+2J implies (A-I)(A+3I)=0 on mean-zero;
    # the constant eigenvalue is 5 and trace zero gives multiplicities.
    return edges


def energy_census(edges: tuple[tuple[int, int], ...]) -> list[int]:
    return [sum(site_pair(s, u, v) == 1 for u, v in edges) for s in SPINS]


def ground_controls(graph: Graph, words: tuple[int, ...], energy: list[int]
                    ) -> tuple[tuple[int, ...], dict[str, object]]:
    minimum = min(energy)
    ground = tuple(s for s in SPINS if energy[s] == minimum)
    need(minimum == 8 and len(ground) == 10, "binary ground census")
    # Match vertices first, before any coordinate chart is used.
    frustrated = tuple(frozenset((u, v) for u, row in enumerate(graph) for v in row
                                if u < v and site_pair(s, u, v) == 1) for s in ground)
    need(all(len({u for p in pairs for u in p}) == N and len(pairs) == 8 for pairs in frustrated),
         "unsatisfied edges are not perfect matchings")
    matchings = set(frustrated)
    need(len(matchings) == 5 and all(a.isdisjoint(b) for a, b in combinations(matchings, 2)),
         "five orientations do not partition all edges")
    chi = tuple(sum(int(bool(w & bit)) << i for i, w in enumerate(words)) for bit in (1, 2, 4, 8, 16))
    need(set(ground) == set(chi) | {s ^ ALL for s in chi}, "ground is not exactly the signed single characters")
    for s in chi:
        need(all(sum(site_pair(s, v, y) for y in row) == -3 for v, row in enumerate(graph)),
             "character is not in the -3 eigenspace")
    products = tuple(a ^ b for a, b in combinations(chi, 2))
    need(len(set(products)) == 10 and all((a ^ b).bit_count() == 8
                                         for a, b in combinations((*products, 0), 2)),
         "pair-product characters not independent")
    return ground, {"minimum_unsatisfied_edges": minimum, "ground_configurations": len(ground),
                    "frustrated_perfect_matchings": len(matchings), "global_signs_per_matching": 2,
                    "edge_partition_by_five_ground_matchings": True,
                    "orientation_character_masks_in_fixture_numbering": list(chi)}


def reference_covariance(graph: Graph, ground: tuple[int, ...]
                         ) -> tuple[dict[tuple[int, int, int], int], dict[str, object]]:
    # No charge table or matrix projector enters this enumeration.
    pair = {(u, v): Fraction(sum(site_pair(s, u, v) for s in ground), len(ground))
            for u in range(N) for v in range(N)}
    expected = {0: Fraction(1), 1: Fraction(-3, 5), 2: Fraction(1, 5)}
    need(all(g == expected[0 if u == v else 1 if v in graph[u] else 2] for (u, v), g in pair.items()),
         "ensemble two-spin kernel differs")
    q = {}
    censuses = set()
    plus_count = set()
    frame_count = 0
    for root, ns in enumerate(graph):
        for mark in set(range(N)) - ns - {root}:
            frame_count += 1
            x = [site_pair(s, root, mark) for s in ground]
            plus_count.add(x.count(1))
            same_frame = Counter()
            for v in range(N):
                y = [site_pair(s, root, v) for s in ground]
                xy = Fraction(sum(a*b for a, b in zip(x, y, strict=True)), len(ground))
                cov = xy - Fraction(sum(x)*sum(y), len(ground)**2)
                conditional = {p: [b for a, b in zip(x, y, strict=True) if a == p] for p in (-1, 1)}
                delta = Fraction(sum(conditional[1]), len(conditional[1])) - Fraction(
                    sum(conditional[-1]), len(conditional[-1]))
                value = cov * Fraction(25, 4)
                need(xy == pair[mark, v] and value == 3*delta and value.denominator == 1,
                     "relational covariance and binary contrast differ")
                # Fix a spin configuration rather than the ensemble:
                # both readings become constants and covariance is zero.
                one_x, one_y = x[0], y[0]
                need(Fraction(one_x*one_y) - Fraction(one_x)*one_y == 0, "one-state control")
                q[root, mark, v] = int(value)
                same_frame[value] += 1
            censuses.add(tuple(sorted(same_frame.items())))
    need(plus_count == {6} and frame_count == 160, "ordered marks or binary split")
    need(censuses == {((-4, 3), (-3, 2), (0, 1), (1, 6), (2, 3), (6, 1))}, "wrong charge-like orbit census")
    return q, {"ordered_root_mark_frames": frame_count, "measured_frame_entries": len(q),
               "pair_kernel_by_distance": {str(k): str(v) for k, v in expected.items()},
               "binary_split_by_orientation": {"X_plus": 3, "X_minus": 2},
               "charge_like_multiplicity": {str(x): n for x, n in next(iter(censuses))},
               "covariance_scale": "4q/25", "conditional_mean_difference_scale": "q/3",
               "single_fixed_ground_configuration": "zero covariance; one conditional cell empty"}


def role_t_covariances(g1: Fraction, g2: Fraction) -> dict[str, Fraction]:
    return {"root": Fraction(0), "mark": 1-g2*g2, "adjacent_to_both": g1*(1-g2),
            "adjacent_to_root_only": g2*(1-g1), "adjacent_to_mark_only": g1-g2*g2,
            "adjacent_to_neither": g2*(1-g2)}


def temperatures(graph: Graph, energy: list[int]) -> dict[str, object]:
    counts = Counter(energy)
    moments: Counter = Counter()
    # m^2 determines the total signed census over all pairs. At each
    # energy use shell transitivity to infer each edge/nonedge average.
    for spin, b in enumerate(energy):
        moments[b] += (N-2*spin.bit_count())**2
    rws = {}
    r = 0
    t = min(set(range(N)) - graph[r] - {r})
    overlap = min(graph[r] & graph[t])
    for x in (Fraction(0), Fraction(1, 8), Fraction(1, 4), Fraction(1, 2), Fraction(1)):
        w = {b: x**(b-8) for b in counts}
        z = sum(n*w[b] for b, n in counts.items())
        bad = sum(b*n*w[b] for b, n in counts.items()) / z
        m2 = sum(v*w[b] for b, v in moments.items()) / z
        g1 = bad/20 - 1
        g2 = ((m2-N)/2 - (2*bad-40))/80
        cov = role_t_covariances(g1, g2)
        # Independent weighted pair checks at one nonedge and two edges.
        for a, b, expected in ((r, t, g2), (r, overlap, g1), (t, overlap, g1)):
            observed = sum(site_pair(s, a, b)*w[e] for s, e in enumerate(energy))/z
            need(observed == expected, "weighted shell symmetry check")
        reference = role_t_covariances(Fraction(-3, 5), Fraction(1, 5))
        proportional = all(cov[k]*reference["mark"] == reference[k]*cov["mark"] for k in cov)
        need(proportional == (x == 0) and ((x > 0) == (bad > 8)), "finite-temperature control")
        rws[str(x)] = {"ground_probability": str(10/z), "expected_unsatisfied_edges": str(bad),
                       "G1": str(g1), "G2": str(g2),
                       "marks_and_common_neighbor_covariances": [str(cov["mark"]), str(cov["adjacent_to_both"])],
                       "all_roles_proportional_to_ground_charge_like_profile": proportional}
    return rws


def certify_orbit_symmetry(graph: Graph, words: tuple[int, ...], ground: tuple[int, ...]) -> dict[str, object]:
    labels = {w: i for i, w in enumerate(words)}
    moves = [tuple(labels[x ^ y] for x in words) for y in words]
    for j in range(4):
        bit_mask = 3 << j
        moves.append(tuple(labels[x ^ bit_mask] if ((x >> j) & 3) in (1, 2) else labels[x] for x in words))
    need(all(all({move[v] for v in row} == graph[move[u]] for u, row in enumerate(graph)) for move in moves),
         "fixture symmetries do not preserve graph")

    def orbit(seed, maps, act):
        seen = {seed}
        queue = deque([seed])
        while queue:
            x = queue.popleft()
            for m in maps:
                y = act(m, x)
                if y not in seen:
                    seen.add(y)
                    queue.append(y)
        return seen

    def permute_spin(move, mask):
        return sum(((mask >> i) & 1) << j for i, j in enumerate(move))

    mark = min(set(range(N)) - graph[0] - {0})
    edge = min(graph[0])
    edge_orbit, other_orbit = (orbit((0, j), moves, lambda m, pair: (m[pair[0]], m[pair[1]]))
                              for j in (edge, mark))
    grounded = orbit(ground[0], moves, permute_spin)
    grounded |= {s ^ ALL for s in grounded}
    need(len(edge_orbit) == 80 and len(other_orbit) == 160 and grounded == set(ground),
         "edge, nonedge, or sign-extended ground transitivity")
    return {"ordered_edge_orbit": len(edge_orbit), "ordered_nonedge_orbit": len(other_orbit),
            "ground_orbit_with_global_spin_flip": len(grounded)}


def states_below_barrier(energy: list[int], initial: tuple[int, ...], threshold: int) -> set[int]:
    reach = set(initial)
    pending = deque(initial)
    while pending:
        s = pending.popleft()
        for i in range(N):
            t = s ^ (1 << i)
            if t not in reach and energy[t] <= threshold:
                reach.add(t)
                pending.append(t)
    return reach


def descent(energy: list[int], ground: tuple[int, ...], edges: tuple[tuple[int, int], ...]) -> dict[str, object]:
    success = [Fraction(0)] * len(energy)
    terminal = [-1] * len(energy)
    stable: Counter = Counter()
    traps = []
    for s in sorted(SPINS, key=energy.__getitem__):
        children = tuple(s ^ (1 << k) for k in range(N) if energy[s ^ (1 << k)] < energy[s])
        if not children:
            stable[energy[s]] += 1
            terminal[s] = s
            if energy[s] == 8:
                success[s] = Fraction(1)
            else:
                traps.append(s)
        else:
            success[s] = sum(success[x] for x in children)/len(children)
            terminal[s] = terminal[children[0]]  # deliberately label-biased scheduler
    need(stable == {8: 10, 12: 80}, "zero-temperature descent local minima")
    p_ground = sum(success)/len(success)
    need(all(s.bit_count() == 8 for s in (*ground, *traps)), "terminal magnetization changed")
    g1 = (8*p_ground+12*(1-p_ground))/20-1
    g2 = (-8-40*g1)/80  # mean-zero spin states: sum over all pairs is -8
    reach_12 = states_below_barrier(energy, ground, 12)
    reach_13 = states_below_barrier(energy, ground, 13)
    need(not reach_12.intersection(traps) and set(traps) <= reach_13, "trap barrier changed")
    all_ground = set(ground)
    first_orientation_threshold = next(h for h in range(8, 41)
                                       if all_ground <= states_below_barrier(energy, ground[:1], h))
    toggles = tuple((1 << u) | (1 << v) for u, v in edges)
    for state in traps:
        neutral = tuple(state ^ flip for flip in toggles if energy[state ^ flip] == 12)
        need(len(neutral) == 12
             and all(any(energy[t ^ (1 << i)] < 12 for i in range(N)) for t in neutral),
             "local neutral two-spin escape failed")
    need(all(energy[spin ^ flip] > 8 for spin in ground for flip in toggles), "ground not absorbing for pair rule")
    basins = Counter(terminal)
    orientation_basins = [basins[s]+basins[s ^ ALL] for s in ground if s < (s ^ ALL)]
    return {"one_spin_stable_states_by_energy": dict(sorted(stable.items())),
            "example_trap_spin_mask": min(traps),
            "all_traps_reach_some_ground_with_max_energy": 13,
            "minimum_max_energy_connecting_all_ground_states": first_orientation_threshold,
            "uniform_initial_uniform_strict_improvement_ground_probability": str(p_ground),
            "same_probability_decimal": f"{float(p_ground):.9f}",
            "unconditioned_equivariant_termination_pair_kernel": {"G1": str(g1), "G2": str(g2)},
            "conditional_uniform_orientation": "requires accepting only actual ground states; follows from symmetry",
            "lowest_local_index_scheduler_ground_orientation_basin_sizes": sorted(orientation_basins),
            "additional_local_simultaneous_pair_update": {
                "neutral_edges_per_trap": 12, "all_neutral_trap_exits_allow_improving_single_flip": True,
                "number_of_proposals": N + len(edges),
                "some_monotone_ground_path_length_at_most": 33,
                "ground_absorbing": True,
                "symmetric_initial_and_uniform_proposals_yield": "uniform ground ensemble in infinite-time limit",
                "finite_time_guarantee": False,
            }}


def matrix_mul(a: Matrix, b: Matrix) -> Matrix:
    n = len(a)
    return tuple(tuple(sum(a[i][k]*b[k][j] for k in range(n)) for j in range(n)) for i in range(n))


def compare_dirichlet_after_spin_audit(graph: Graph, q: dict[tuple[int, int, int], int]) -> dict[str, object]:
    n = N-1
    comparisons = 0
    for root, ns in enumerate(graph):
        live = tuple(v for v in range(N) if v != root)
        a = tuple(tuple(int(v in graph[u]) for v in live) for u in live)
        a2 = matrix_mul(a, a)
        a3 = matrix_mul(a2, a)
        p40 = tuple(tuple(-a3[i][j]+4*a2[i][j]+5*a[i][j]-8*int(i == j) for j in range(n))
                    for i in range(n))
        for j, t in enumerate(live):
            if t in ns:
                continue
            for i, v in enumerate(live):
                need(p40[i][j] == 2*q[root, t, v], "independent Dirichlet comparator disagrees")
                comparisons += 1
    return {"checked_live_cells": comparisons, "relation": "P_D delta_t=q/20",
            "used_for_ground_ensemble_or_inferred_binary_covariance": False}


def probe() -> dict[str, object]:
    graph, words = folded_fixture()
    edges = spectra_certificate(graph)
    energy = energy_census(edges)
    ground, ground_report = ground_controls(graph, words, energy)
    q, binary_report = reference_covariance(graph, ground)
    return {"scope": "finite binary ensemble/energy only; no hopping charge or physical outcome law",
            "assignments": len(energy), "energy_histogram": dict(sorted(Counter(energy).items())),
            "ground": ground_report, "binary_ensemble": binary_report,
            "ensemble_symmetries": certify_orbit_symmetry(graph, words, ground),
            "finite_temperatures": temperatures(graph, energy), "one_spin_descent": descent(energy, ground, edges),
            "downstream_dirichlet_comparator": compare_dirichlet_after_spin_audit(graph, q)}


if __name__ == "__main__":
    print(json.dumps(probe(), sort_keys=True, separators=(",", ":")))
