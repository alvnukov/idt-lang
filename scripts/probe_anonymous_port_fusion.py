"""Can an anonymous local collision create height two from a binary preparation?

Assume m co-located ports with integer loads, one synchronous deterministic
bijective update, total conservation and equivariance under the FULL S_m
acting on port positions. No additional local state, named unit or source.
These are supplied collision resources, not a derivation of a merger.

For k input ones and m-k zeroes, a site's value after the map is constant
on the occupied block (a) and on the empty block (b), by its stabilizer.
An equivariant bijection preserves stabilizers in both directions. For
0<k<m, k*a+(m-k)*b=k leaves identity, or a=0 and b=k/(m-k) if integral.
This second option is real: transpose the two patterns for every choice
of occupied set (ordinary complement when b=1). There are no collisions
between the specified pairs, and the extension by identity is reversible.
In fact if chosen the inverse on this block is forced: the same stabilizer
fixes only these two total-k outputs. Uniform zero and all ones are fixed.
Thus one or two ports cannot create height two from binary input; the
two-port singleton CAN switch ports. With three ports and two units only
identity or 110<->002 and its permutations are possible. It is the unique
nontrivial anonymous update on this sector, not forced by anonymity alone.

On a finite simple undirected cubic graph a slice gives incoming integer
loads on directed edges. Scatter simultaneously, then propagate outputs
on the corresponding edges, with no resident stock. Singleton input must
reflect onto its arrival edge (three-port symmetry). For the fusion rule,
each undirected edge carries one orbit of length six: two singles enter
one endpoint, double goes to the other, splits to its other neighbors,
both singles reflect, double returns and splits; singles reflect again.
All other binary slices have distinct heads AND distinct tails and merely
reverse. Opposite directed arcs on ONE edge give period ONE as an unlabelled
occupancy, all other idle slices period two. Exact statement for two units
only; simple cubic wiring and synchronous arrivals are essential inputs.

The optional reversible observer has one additional bit at every vertex,
updated by XOR on an arriving double. This is local without distinguished
ports, but it is extra memory, not a detector secretly present in two units.
An active orbit flips the central edge's two bits in six ticks and resets
in twelve. This records parity, not permanent detection or external flux.

Older moving/parked comparator (probe_indistinguishable_mobile_load.py)
has different degrees of freedom and an externally supplied through-port.
Here two separate singles can become a mobile double without any prepared
double. No parked site exists here. Delivering that double, capturing it
or adding a second preparation are bridges. In the older exchange (k,s)
->(1+s,k-1), (2,0)->(1,1), not (1,2); its mixed (2,2) needs four units.
No particles, independent trials or physical collision law are inferred.
"""

import json
from collections import Counter
from itertools import combinations_with_replacement, permutations

from scripts.probe_indistinguishable_mobile_load import exchange as moving_parked_exchange
from scripts.probe_indistinguishable_mobile_load import extremes_only as moving_parked_extremes


def need(test, why):
    if not test:
        raise AssertionError(why)


def compositions(total, m):
    """All weak m-part compositions of total."""
    if m == 1:
        yield (total,)
        return
    for x in range(total+1):
        for tail in compositions(total-x, m-1):
            yield (x, *tail)


def binary_exits(m, k):
    start = (1,)*k + (0,)*(m-k)
    if k in (0, m) or k % (m-k):
        return [start]
    return [start, (0,)*k + (k//(m-k),)*(m-k)]


def local(m, k, loads):
    """An actual equivariant involution on all loads, extended by identity."""
    if not 0 < k < m or k % (m-k) or sum(loads) != k:
        return loads
    b = k//(m-k)
    if all(x in (0, 1) for x in loads):
        return tuple(0 if x else b for x in loads)
    if all(x in (0, b) for x in loads):
        return tuple(0 if x else 1 for x in loads)
    return loads


def permute(v, p):
    return tuple(v[j] for j in p)


def local_controls():
    audited = 0
    for m in range(1, 7):
        swaps = [tuple(j+1 if j == i else j-1 if j == i+1 else j for j in range(m)) for i in range(m-1)]
        for k in range(m+1):
            start, *rest = binary_exits(m, k)
            keep = [p for p in swaps if permute(start, p) == start]
            loads = list(compositions(k, m))
            actual = {v for v in loads if all(permute(v, p) == v for p in keep)}
            need(actual == {start, *rest}, "exhaustive stabilizer outputs disagree with the formula")
            need(local(m,k,start) == (rest[0] if rest else start), "exit construction failed")
            for v in loads:
                out = local(m,k,v)
                need(sum(out) == sum(v) and local(m,k,out) == v and
                     all(permute(out,p) == local(m,k,permute(v,p)) for p in swaps), "extension is not equivariant")
            audited += 1
    # Independent brute enumeration of ALL bijections within each complete
    # three-port sector of total 0, 1 or 2, testing all six port permutations.
    rows = {}
    for total in (0,1,2):
        ways = tuple(compositions(total, 3))
        allowed = []
        for perm in permutations(ways):
            f = dict(zip(ways, perm))
            if all(f[permute(v,p)] == permute(f[v],p) for v in ways for p in permutations(range(3))):
                allowed.append(perm)
        need(set(allowed) == {ways, tuple(local(3,2,v) for v in ways)}, "unexpected anonymous route")
        rows[total] = len(allowed)
    # A named two-port involution can bunch: it violates precisely exchange
    # symmetry (the swapped binary input is still (1,1), but the output changes).
    biased = {(1,1):(2,0), (2,0):(1,1), (0,2):(0,2)}
    need(all(biased[y] == x and sum(x) == sum(y) for x,y in biased.items()) and
         biased[(1,1)][::-1] != biased[(1,1)], "named-port negative control")
    return {"binary_shells_on_1_to_6_ports": audited, "three_port_route_counts_by_total": rows,
            "smallest_height_two": {"ports": 3, "input": [1,1,0], "output": [0,0,2]},
            "four_port_height_three_control": binary_exits(4,3)[1]}


def build_graph(kind):
    if kind == "K4":
        a = [set(range(4))-{i} for i in range(4)]
    elif kind == "K3,3":
        a = [set(range(3,6)) if i < 3 else set(range(3)) for i in range(6)]
    elif kind == "cube":
        a = [{i^(1<<j) for j in range(3)} for i in range(8)]
    else:
        raise ValueError(kind)
    need(all(len(s) == 3 and i not in s and all(i in a[j] for j in s) for i,s in enumerate(a)),
         "not a simple reciprocal cubic graph")
    return tuple(tuple(sorted(s)) for s in a)


def state(*arcs):
    return tuple(sorted(arcs))


def reverse(w):
    return state(*((v,u) for u,v in w))


def tick(graph, w, fusion=True):
    incoming = Counter(w)
    output = []
    for v, ports in enumerate(graph):
        loads = tuple(incoming[u,v] for u in ports)
        after = local(3, 2, loads) if fusion else loads
        for u, k in zip(ports, after):
            output.extend([(v,u)] * k)
    need(len(output) == len(w), "unit lost or input not on a wire")
    return state(*output)


def observer_tick(graph, w, bits):
    if w[0] == w[1]:
        bits ^= 1 << w[0][1]
    return tick(graph,w), bits


def six(graph, v, c):
    a,b = (i for i in graph[v] if i != c)
    x,y = (i for i in graph[c] if i != v)
    return (state((a,v),(b,v)), state((v,c),(v,c)), state((c,x),(c,y)),
            state((x,c),(y,c)), state((c,v),(c,v)), state((v,a),(v,b)))


def global_controls(kind):
    g = build_graph(kind)
    arcs = sorted((u,v) for u, ports in enumerate(g) for v in ports)
    edges = [(u,v) for u,v in arcs if u<v]
    states = set(combinations_with_replacement(arcs, 2))
    moves = {s:tick(g,s) for s in states}
    need(set(moves.values()) == states and all(reverse(tick(g,reverse(t))) == s for s,t in moves.items()),
         "full graph map is not reversible/conservative")
    active = set()
    for v,c in edges:
        orbit = six(g,v,c)
        need(len(set(orbit)) == 6 and active.isdisjoint(orbit) and
             all(moves[s] == orbit[(k+1)%6] for k,s in enumerate(orbit)), "not the proposed six-slice orbit")
        active.update(orbit)
        # At two opposite co-arrival ends of this central edge, reversing
        # just one incoming arc shifts ONLY that singleton's phase by one.
        for k in (0,3):
            (a,h), other = orbit[k]
            delayed = state((h,a),other)
            need(moves[delayed] == reverse(delayed) != delayed and moves[moves[delayed]] == delayed,
                 "desynchronized input still fused")
        # Closed, explicit observer: no ID, passive chronology, or sink is
        # built into the underlying bare collision. The local bits cost stock
        # of available memory locations and are counted separately.
        first = cur = orbit[0]
        bits = 0
        for t in range(1, 13):
            cur,bits = observer_tick(g,cur,bits)
            need((cur == first and bits == 0) == (t == 12), "closed recorder period")
            if t == 6:
                need(bits == (1<<v) | (1<<c), "recorder failed to identify both double arrivals")
    cycles = Counter()
    unseen = states.copy()
    while unseen:
        s = next(iter(unseen))
        cur = s
        length = 0
        while cur in unseen:
            unseen.remove(cur)
            cur = moves[cur]
            length += 1
        need(cur == s, "not a permutation orbit")
        cycles[length] += 1
    inactive = states-active
    for s in inactive:
        ((a,b),(c,d)) = s
        need(a != c and b != d and moves[s] == reverse(s) and (moves[s] == s) == ((a,b) == (d,c)),
             "idle occupancy period not explained by reflection")
    binary = {s for s in states if s[0] != s[1]}
    need(all((s in active) == (s[0][0] == s[1][0] or s[0][1] == s[1][1]) for s in binary)
         and all(tick(g,s,False) == reverse(s) for s in binary), "binary reachability or identity control")
    e = len(edges)
    need(cycles == {1:e, 2:(len(states)-7*e)//2, 6:e} and len(active & binary) == 4*e,
         "global orbit census")
    return {"vertices":len(g), "undirected_edges":e, "all_two_unit_slices":len(states),
            "binary_preparations":len(binary), "binary_preparations_reaching_double":len(active & binary),
            "bare_orbits_by_period":dict(sorted(cycles.items())), "active_period_with_local_parity_recorders":12}


def probe():
    need(moving_parked_exchange(2,0) == (1,1) and moving_parked_exchange(3,0) == (1,2) and
         (moving_parked_exchange(2,2),moving_parked_extremes(2,2)) == ((3,1),(2,2)),
         "old comparator boundary no longer matches the separately supplied interface")
    return {"scope":"input-independent anonymous S_m collision; cubic synchronous propagation supplied; "
                    "exact reversible finite mechanism, not particle or empirical status",
            "local":local_controls(), "networks":{g:global_controls(g) for g in ("K4","K3,3","cube")},
            "K4_example_incoming_arc_pairs":six(build_graph("K4"),0,1),
            "stock_boundary":"Mobile double reachable from binary arcs; no parked kind or transfer interface. "
                             "Old exchange(2,0)=(1,1); the mixed comparator (2,2) uses four units."}


if __name__ == "__main__":
    print(json.dumps(probe(), separators=(",", ":")))
