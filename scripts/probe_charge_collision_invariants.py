"""Which additive observables survive signed-charge-neutral rearrangements?

A root and a distance-two mark supply the 3+2 chart. We supply q=-2C+3W,
fixed arity, and the filter sum(q_out)=sum(q_in). This filter does NOT
explain q, select an actual collision, or set any probabilities or rates.
A blank mask is an actual carrier; repeated preparations are allowed.
The native one-step move T_j flips all bits except j in fixed-sheet
representatives of the folded graph. It is NOT a one-bit step of the cover.

We retain every unordered distinct endpoint pair satisfying the given
contract. Relabeling carriers, direction of time, and multiple ways to
realize the same endpoint pair cannot change an additive conservation law.
For independently chosen ports, all carriers move, even when their steps
cancel in the multiset. No implicit allowance for a carrier to wait.

Each endpoint difference is an integer vector in Z^16. Exact integer row
elimination gives its rank over Q and hence over R. The named independent
vectors in its kernel then describe ALL real diagonal additive invariants.
We also report the dimensions over F2, from the original integer rows,
not reductions of primitive rational rows. No integral Smith form claim.
For example, at every even common-port arity the XOR of all masks survives
since an even number of identical translations cancel. This is a genuine
finite-valued law, not an extra real additive conservation law.

All-arity extension: broad replacements allow stationary padding. A legal
native move at arity m embeds at m+2 by adding x and T_j(x), exchanging
them using the same j, preserving its entire endpoint difference. For a
common port let h be the number whose held bit is occupied, and Q the input
charge. Charge neutrality is Q=m-2h for a held color, and 2Q=-3m+6h for
a held weak bit (sum the bitwise changes). At odd arity only a held color is
possible; both weak bits flip together, preserving I=[W=1] individually.
Thus from arities 3,4 the common laws are (1,q,I) for every odd m>=3
and (1,q) for every even m>=4. Independent ports give (1,q) for all m>=3.
Broad replacements also give (1,q) for all m>=3.

Independently of topology, a signed-neutral conversion has occupation
differences (3k,2k); total occupied-bit difference is 5k and even, so k
must be even. For one or two carriers the range of total occupation on
either sheet has width 4m<10. Hence both C and W separately survive there.
All results are about additive functions of the 16 individual states, not
all possible joint functions of an entire preparation, nor any physical
baryon/lepton numbers or field gauge.
"""

from __future__ import annotations

import json
from collections import Counter, defaultdict
from itertools import combinations, combinations_with_replacement, product
from math import gcd

if __package__:
    from . import probe_marked_carrier_charge as marked
else:
    import probe_marked_carrier_charge as marked


PORTS = tuple(range(5))
ALL = 31
WEAK = 24


def need(test, why):
    if not test:
        raise ArithmeticError(why)


def step(x, j):
    return x ^ ALL ^ (1 << j)


def chart_check():
    graph = marked.anonymous_fixture()
    root, cover = min(graph), marked.double_cover(graph)
    _, chart = marked.recover_cover_coordinates(cover, root)
    mark, = (v for v in graph if chart[v, 0] == WEAK)
    block, _, _ = marked.port_block(graph, cover, root, mark)
    need(block == WEAK, "nonneighbor did not select the 3+2 partition")
    for v in graph:
        for s in (0, 1):
            x = chart[v, s]
            need({chart[w, s] for w in graph[v]} == {step(x, j) for j in PORTS},
                 "chart moves must equal exactly one projected base hop")
            need(chart[v, s ^ 1] == (x ^ ALL), "sheet conjugacy")


C, W = zip(*(marked.occupations(x, WEAK) for x in range(32)), strict=True)
Q = tuple(-2*c + 3*w for c, w in zip(C, W, strict=True))
I = tuple(int(w == 1) for w in W)


def total(cfg, f):
    return sum(f[x] for x in cfg)


def primitive(v):
    d = gcd(*v)
    return [x // d for x in v] if d > 1 else v


def rank_q(rows):
    pivots = {}
    for row in sorted(rows):
        v = list(row)
        for p, b in sorted(pivots.items()):
            if v[p]:
                a, d = v[p], b[p]
                v = primitive([d*x - a*y for x, y in zip(v, b, strict=True)])
        p = next((k for k, x in enumerate(v) if x), None)
        if p is not None:
            pivots[p] = primitive(v)
    return len(pivots)


def rank_f2(rows):
    pivots = {}
    for row in rows:
        v = sum((x % 2) << k for k, x in enumerate(row))
        while v:
            p = v.bit_length() - 1
            if p not in pivots:
                pivots[p] = v
                break
            v ^= pivots[p]
    return len(pivots)


def named_basis(states, m, mode):
    level_indicators = [tuple(int(Q[x] == q) for x in states) for q in sorted({Q[x] for x in states})]
    if m == 1 and mode != "broad":
        joined_level = 1 if states[0] == 0 else -1
        # Only this six-state charge level is connected by neutral one-steps.
        groups = [tuple(x for x in states if Q[x] == joined_level)]
        groups += [(x,) for x in states if Q[x] != joined_level]
        return "neutral components", [tuple(int(x in group) for x in states) for group in groups]
    if (mode == "broad" and m == 1) or (mode != "broad" and m == 2):
        return "charge-level indicators", level_indicators
    fields = {"1": (1,)*32, "C": C, "W": W, "q": Q, "I": I}
    names = ("1", "C", "W") if mode == "broad" and m == 2 else (
        ("1", "q", "I") if mode == "common" and m % 2 else ("1", "q"))
    return ",".join(names), [tuple(fields[n][x] for x in states) for n in names]


def census(states, m, mode):
    configs = tuple(combinations_with_replacement(states, m))
    charge = {cfg: total(cfg, Q) for cfg in configs}
    color = {cfg: total(cfg, C) for cfg in configs}
    grouped = defaultdict(list)
    for cfg in configs:
        grouped[charge[cfg]].append(cfg)
    rows, zero_rows, conversion_sectors = set(), set(), set()
    pairs = 0
    indices = {x: k for k, x in enumerate(states)}

    def record(s, t):
        nonlocal pairs
        pairs += 1
        v = [0]*len(states)
        for x, y in zip(s, t, strict=True):
            v[indices[y]] += 1
            v[indices[x]] -= 1
        # Opposite orientations define the same linear constraint, even mod 2.
        row = tuple(v if next(z for z in v if z) > 0 else (-z for z in v))
        rows.add(row)
        if charge[s] == 0:
            zero_rows.add(row)
        if color[s] != color[t]:
            conversion_sectors.add(charge[s])

    if mode == "broad":
        for group in grouped.values():
            for s, t in combinations(group, 2):
                record(s, t)
    else:
        neighbours = {x: tuple(step(x, j) for j in PORTS) for x in states}
        for s in configs:
            destinations = (zip(*(neighbours[x] for x in s), strict=True) if mode == "common"
                            else product(*(neighbours[x] for x in s)))
            for t in {tuple(sorted(dst)) for dst in destinations}:
                if s < t and charge[s] == charge[t]:
                    record(s, t)
    label, basis = named_basis(states, m, mode)
    kernel_dim = len(states) - rank_q(rows)
    need(rank_q(basis) == len(basis) == kernel_dim, "basis dimension: " + repr((m, mode, label)))
    for r in rows:
        need(all(sum(x*y for x, y in zip(r, b, strict=True)) == 0 for b in basis), "basis fails")
    return {"pairs": pairs, "rows_up_to_sign": len(rows), "dim_real": kernel_dim, "basis": label,
            "dim_F2": len(states)-rank_f2(rows), "dim_real_only_Q0": len(states)-rank_q(zero_rows),
            "conversion_Q": sorted(conversion_sectors)}


def witness(start, ports, end=None):
    if ports is not None:
        target = tuple(step(x, j) for x, j in zip(start, ports, strict=True))
        need(end is None or target == end, "misidentified primitive witness")
        end = target
    need(all(x.bit_count() % 2 == 0 for x in (*start, *end)), "wrong witness sheet")
    need(total(start, Q) == total(end, Q), "witness is not signed neutral")
    need(total(start, C) != total(end, C), "witness fails to convert occupation")
    return {"start": start, "end": end, "ports": ports, "Q": total(start, Q),
            "C": [total(cfg, C) for cfg in (start, end)], "W": [total(cfg, W) for cfg in (start, end)],
            "I": [total(cfg, I) for cfg in (start, end)]}


def occupancy_switch(cfg):
    """One sparse coordinated collision, specified without evaluating Q.

    An ordered carrier tuple is allowed; rule does not use carrier labels.
    Idle for other inputs, unlike the mandatory-movement census. The 3+2
    partition and this specially chosen pair of patterns are inputs.
    """
    counts = Counter(cfg)
    if sorted(counts.values()) != [1, 2]:
        return cfg
    repeated, = (x for x in counts if counts[x] == 2)
    single, = (x for x in counts if counts[x] == 1)
    if repeated == 0 and (C[single], W[single]) == (1, 1):
        held_color = single & 7
    elif (C[repeated], W[repeated], C[single], W[single]) == (2, 2, 3, 1):
        held_color = (repeated & 7) ^ 7
    else:
        return cfg
    need(held_color.bit_count() == 1, "switch requires an unambiguous held color")
    return tuple(step(x, held_color.bit_length()-1) for x in cfg)


def switch_control(even):
    changed, relations, rows = 0, set(), set()
    for s in product(even, repeat=3):
        t = occupancy_switch(s)
        need(occupancy_switch(t) == s and total(t, Q) == total(s, Q), "switch reversibility/charge")
        if t != s:
            changed += 1
            a, b = sorted((tuple(sorted(s)), tuple(sorted(t))))
            relations.add((a, b))
            rows.add(tuple(b.count(x)-a.count(x) for x in even))
    need(changed == 36 and len(relations) == 6 and rank_q(rows) == 6, "sparse switch census")
    # For any independent product of local maps conserving sum q on ALL
    # tuples, changing just the ith input forces its charge increment to be
    # constant. At a charge minimum it is nonnegative, at a maximum it is
    # nonpositive: each such constant is zero. No exchange by this route.
    # A common, input-independent random seed independent of preparations
    # does not rescue an almost-sure law: there are only finitely many inputs.
    need(all(Q[step(0, j)] != Q[0] for j in PORTS), "a blank has no same-charge hop")
    return {"ordered_inputs": len(even)**3, "ordered_inputs_moved": changed,
            "unordered_exchanges": len(relations), "dim_real": len(even)-rank_q(rows),
            "occupation_linear_constraint": "6*a+4*b=0 for a*C+b*W",
            "scope": "chosen 3+2 pattern-based collision, identity elsewhere; not a derivation of the rule"}


def probe():
    chart_check()
    even = tuple(x for x in range(32) if x.bit_count() % 2 == 0)
    odd = tuple(x for x in range(32) if x.bit_count() % 2 == 1)
    for x in even:
        y = x ^ ALL
        need((C[y], W[y], Q[y], I[y]) == (3-C[x], 2-W[x], -Q[x], I[x]), "mirror readout")
        need(all(step(x, j) ^ ALL == step(y, j) for j in PORTS), "mirror native maps")
    checks = [(m, mode) for m in (1, 2, 3) for mode in ("broad", "common", "independent")]
    checks.append((4, "common"))
    results = {}
    for m, mode in checks:
        a, b = (census(sheet, m, mode) for sheet in (even, odd))
        need({**a, "conversion_Q": sorted(-q for q in a["conversion_Q"])} == b, "mirror census")
        results[f"{m}:{mode}"] = a
    for mode, expected in (("broad", [-4, 0, 1, 6]), ("common", [1]), ("independent", [-4, 1])):
        need(results[f"3:{mode}"]["conversion_Q"] == expected, "signed conversion sectors")
    # In the formula for a common port, evaluate Q_out+Q_in on individual
    # states, hence also on every multiset by linearity.
    for x in range(32):
        for j in PORTS:
            held = (x >> j) & 1
            need(Q[step(x, j)] + Q[x] == (2-4*held if j < 3 else -3+6*held), "held-port rule")
            need(j >= 3 or I[step(x, j)] == I[x], "color-held steps must conserve I")
    witnesses = {
        "three_common": witness((0, 0, 9), (0, 0, 0), (30, 30, 23)),
        "three_independent_breaks_I": witness((0, 0, 3), (3, 3, 0), (23, 23, 29)),
        "four_common_breaks_I": witness((0, 0, 0, 15), (3,)*4, (23, 23, 23, 24)),
        "zero_broad_three": witness((0, 0, 0), None, (3, 27, 27)),
        "zero_independent_five": witness((0,)*5, (0, 0, 0, 3, 3)),
        "zero_common_six": witness((0, 0, 0, 3, 27, 27), (0,)*6, (30, 30, 30, 29, 5, 5)),
    }
    # Excluding m<=4 native at strictly zero Q: then C=3k, W=2k,
    # total populated bits N=5k even, so N in {0,10} when m<=4.
    # Any conversion must connect all blanks (N=0) to N=10. All m
    # blanks take one step to N=4m, never ten; reverse by involution.
    # Common m=5 additionally fails both common-port neutrality equations
    # at Q=0 (h=m/2 would not be an integer).
    for m in range(1, 6):
        if m <= 4:
            need(4*m != 10 and 4*m < 20, "all-blank exclusion")
        if m == 5:
            need(all(m != 2*h for h in range(m+1)), "no common odd-arity zero-Q case")
    abs_q, sq_q = tuple(map(abs, Q)), tuple(x*x for x in Q)
    s, t = (0, 0, 9), (30, 30, 23)
    need(([total(x, abs_q) for x in (s, t)], [total(x, sq_q) for x in (s, t)]) == ([1, 7], [1, 17]),
         "unsigned and squared readouts are different collision laws")
    s, t = (0, 3), (27, 27)
    need(total(s, abs_q) == total(t, abs_q) == 4 and (total(s, Q), total(t, Q)) == (-4, 4),
         "unsigned false positive")
    return {"scope": "fixed arity, one sheet at a time, signed-neutral relation; not an interaction law",
            "even_level_counts": sorted(Counter(Q[x] for x in even).items()), "even_census": results,
            "odd_census": "all counts and dimensions identical; conversion_Q sign reversed",
            "occupancy_switch_control": switch_control(even),
            "witnesses_even": witnesses, "first_conversion_at_zero_Q": {"broad": 3, "common": 6, "independent": 5},
            "unsigned_controls": {"signed_neutral_abs": [1, 7], "signed_neutral_squares": [1, 17],
                                  "abs_neutral_signed": [-4, 4]}}


if __name__ == "__main__":
    print(json.dumps(probe(), indent=2, sort_keys=True))
