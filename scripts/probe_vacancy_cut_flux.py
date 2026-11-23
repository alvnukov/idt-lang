"""Actual vacancy transfers on a clamped graph, including unsuccessful proposals.

One occupied source, three binary storage sites, and k_i empty terminal
leaves on arm i. An edge proposal exchanges its two endpoint bits; boundary
bits are immediately restored by external reservoirs. Freeze exactly the
distal change (3,3,3) -> (1,3,3). The raw law does NOT specify a clock.
For independent uniform proposals from all surviving edges, report the
ratio of stationary mean terminal counts, not a mean of finite-window
ratios, first-packet probabilities or physical detection frequencies.

The polarity control complements ALL initial and clamped bits and uses
the identical sequence of edge names. A positive source pulse instead
alters ONE preparation. Do not confuse a positive pulse's downstream
response with particle/hole reversal or a monotone source-injection rate.
"""

from __future__ import annotations

import json
from collections import Counter
from fractions import Fraction as F
from itertools import product

STATES = tuple(product((0, 1), repeat=3))
EMPTY = (0, 0, 0)


def need(ok, reason):
    if not ok:
        raise ArithmeticError(reason)


def edges(k):
    # (i,-1) is the incident edge source -> i; (i,j) points i -> leaf j.
    return tuple((i, j) for i, count in enumerate(k) for j in range(-1, count))


def step(state, edge, complement=False):
    i, leaf = edge
    source, terminal = (0, 1) if complement else (1, 0)
    a, b = (source, state[i]) if leaf < 0 else (state[i], terminal)
    new_a, new_b = b, a
    # Count the signed transfer to the right endpoint, BEFORE clamp restoration.
    out = list(state)
    out[i] = new_b if leaf < 0 else new_a
    return tuple(out), new_b-b


def bit_flip(x):
    return tuple(1-v for v in x)


def solve_stationary(counts, width):
    n = len(counts)
    # Solve pi P=pi and sum pi=1 from the observed transition counts.
    a = [[F(counts[i][j]-width*int(i == j)) for i in range(n)] + [F(0)] for j in range(n-1)]
    a.append([F(1)]*(n+1))
    for j in range(n):
        pivot = next(i for i in range(j, n) if a[i][j])
        a[j], a[pivot] = a[pivot], a[j]
        a[j] = [v/a[j][j] for v in a[j]]
        for i in range(n):
            if i != j:
                factor = a[i][j]
                a[i] = [x-factor*y for x, y in zip(a[i], a[j], strict=True)]
    pi = tuple(row[-1] for row in a)
    need(sum(pi) == 1 and min(pi) > 0 and all(sum(pi[i]*counts[i][j] for i in range(n)) == width*pi[j]
                                              for j in range(n)), "stationary distribution not verified")
    return pi


def iid(k):
    menu = edges(k)
    m = len(menu)
    counts = [[0]*8 for _ in STATES]
    currents = []
    cases = inert = 0
    for i, x in enumerate(STATES):
        row = []
        for edge in menu:
            y, flow = step(x, edge)
            other, sign = step(bit_flip(x), edge, complement=True)
            need(other == bit_flip(y) and sign == -flow, "complement replay changed the schedule or sign")
            site, leaf = edge
            need(all(y[j]-x[j] == (flow if leaf < 0 else -flow)*int(j == site) for j in range(3)),
                 "local stock continuity")
            counts[i][STATES.index(y)] += 1
            row.append(flow)
            cases += 1
            inert += y == x
        currents.append(row)
    pi = solve_stationary(counts, m)
    # Independent product law: each site has ratio occupied:vacant=1:k_i.
    product_pi = []
    for state in STATES:
        weight = F(1)
        for v, count in zip(state, k, strict=True):
            weight *= F(1 if v else count, count+1)
        product_pi.append(weight)
    need(list(pi) == product_pi and cases == 8*m and inert == cases//2, "proposal census or product law")
    flow = {edge: sum(pi[i]*currents[i][j] for i in range(8))/m for j, edge in enumerate(menu)}
    inflow = [flow[i, -1] for i in range(3)]
    outflow = [sum(flow[i, j] for j in range(k[i])) for i in range(3)]
    occupied = [sum(pi[j]*s[i] for j, s in enumerate(STATES)) for i in range(3)]
    for i in range(3):
        # Graph mean balance: with independent proposals, all successful
        # incoming proposals require vacancy, each exit requires occupancy.
        need(1-occupied[i] == k[i]*occupied[i] and inflow[i] == outflow[i] == F(k[i], m*(1+k[i])),
             "raw transfer/equal-edge mean balance")
    return {"leaves": k, "proposal_cases": cases, "inert_cases": inert, "stationary_pi_in_lex_bit_order": list(map(str, pi)),
            "mean_occupancy": list(map(str, occupied)), "source_by_arm_per_proposal": list(map(str, inflow)),
            "terminals_by_arm_per_proposal": list(map(str, outflow)),
            "first_arm_share_of_stationary_exit_flow": str(outflow[0]/sum(outflow)),
            "total_exits_per_uniform_proposal": str(sum(outflow)),
            "total_exits_per_time_if_each_edge_has_unit_rate": str(m*sum(outflow))}


def run(initial, word, complement=False):
    x = initial
    ins, outs = [0]*3, [0]*3
    for e in word:
        i, leaf = e
        x, sign = step(x, e, complement)
        (ins if leaf < 0 else outs)[i] += sign
    need(all(ins[i]-outs[i] == x[i]-initial[i] for i in range(3)), "unaccounted boundary storage")
    return x, tuple(ins), tuple(outs)


def scheduled_controls():
    k = (1, 3, 3)
    def word(grouped):
        operations = []
        for i, n in enumerate(k):
            a, ds = [(i, -1)], [(i, j) for j in range(n)]
            operations.extend((a*2 + ds*2) if i in grouped else (a+ds)*2)
        return operations
    left, right = word({0}), word({1, 2})
    need(Counter(left) == Counter(right) == {e: 2 for e in edges(k)}, "proposal histogram not identical")
    x, a, b = run(EMPTY, left)
    y, c, d = run(EMPTY, right)
    need(x == y == EMPTY and a == b == (1, 2, 2) and c == d == (2, 1, 1), "closed-window clock effect")
    need(run(bit_flip(EMPTY), left, True) == (bit_flip(x), tuple(-v for v in a), tuple(-v for v in b)),
         "complement closed trajectory")
    transient, inc, out = run(EMPTY, [(0, -1)])
    need(transient == (1, 0, 0) and inc == (1, 0, 0) and out == EMPTY, "an open window need not balance the two cuts")
    return {"repeated_periods_start_and_finish_empty": True, "proposals_per_surviving_edge_per_period": 2,
            "first_arm_grouped": {"terminal_counts": b, "first_share": str(F(b[0], sum(b)))},
            "other_arms_grouped": {"terminal_counts": d, "first_share": str(F(d[0], sum(d)))},
            "open_window": {"one_incident_transfer": inc, "terminal_counts": out, "stored": transient}}


def pulse_control(k):
    # Start just after one successful extra source deposition, and couple
    # every subsequent proposal. Ordered states differ in at most one bit.
    # Each nonnegative discrepancy survives, exits at a terminal, or blocks
    # a later source injection. Check an induction step for every such pair.
    exact_cases = 0
    for low, high in product(STATES, repeat=2):
        gap = sum(high)-sum(low)
        if gap not in (0, 1) or any(u > v for u, v in zip(low, high, strict=True)):
            continue
        for edge in edges(k):
            lo, f0 = step(low, edge)
            hi, f1 = step(high, edge)
            delta = f1-f0
            remain = sum(hi)-sum(lo)
            need(all(u <= v for u, v in zip(lo, hi, strict=True)) and 0 <= remain <= gap, "coupling order")
            need((delta in (-1, 0) and remain == gap+delta) if edge[1] < 0
                 else (delta in (0, 1) and remain == gap-delta), "negative downstream or proliferating pulse")
            exact_cases += 1
    low, high = EMPTY, (1, 0, 0)
    _, a = step(low, (0, -1))
    _, b = step(high, (0, -1))
    need(b-a == -1 and exact_cases == 20*len(edges(k)), "source-current countercontrol")
    return {"ordered_pairs_times_proposals": exact_cases, "later_source_injection_difference_can_be": b-a,
            "downstream_cumulative_extra_exits_after_one_positive_deposition": [0, 1],
            "scope": "same fixed schedule, no negative downstream lobe; future incident current need not increase"}


def probe():
    before, after = iid((3, 3, 3)), iid((1, 3, 3))
    need((before["first_arm_share_of_stationary_exit_flow"], after["first_arm_share_of_stationary_exit_flow"]) ==
         ("1/3", "1/4"), "frozen fork shares")
    return {"scope": "finite_clamped_bits_and_supplied_clock_not_a_wave_or_measured_click_law",
            "before": before, "after": after, "alternative_post_cut_charts":
                {"single_uniform_arm_choice_without_feedback": "1/3", "uniform_remaining_leaves": "1/7"},
            "deterministic_and_open_window_controls": scheduled_controls(),
            "coupled_positive_pulse": pulse_control((1, 3, 3))}


if __name__ == "__main__":
    print(json.dumps(probe(), sort_keys=True))
