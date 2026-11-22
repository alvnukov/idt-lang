"""Locally reversible, finite-speed petal clocks. Finite construction only.

On each logical edge there are two reciprocal lanes. At each interior
junction swap the lane bit with a stored bit and exit on the opposite side.
At the hub use the same petal for lane 0 and the cyclic successor for lane
1 (predecessor if traversed backwards). A private even-length wire per lane
makes the physical graph simple and bipartite, including the one-cell loop.
Each of the three local rules is an involution on ALL its local states.
Each reported tick traverses exactly one physical edge. The lane carries the
marker; the moving cursor is not itself identified as an incident particle.

Launch on lane 1. On an n-edge petal, one circuit swaps the incoming bit
through n-1 cells: the n slots rotate once. With initially blank cells the
mark reaches the hub every n laps, costing 4 n² ticks at uniform spacing 4.
Generally q_i = 1 + initial marked cells in petal i. Consecutive visits take
successive cyclic gaps between ones. Every q_i visits take n_i complete laps
and restore its cells. In L = lcm(q_i) tours, time on rail i is
L*n_i*perimeter_i/q_i, with arbitrary ordering and either traversal direction.
This timing formula assumes the two lanes of a logical edge have equal length.

Stationarity is different: uniform over directed arcs AND all compatible
registers is invariant under the global permutation. Uniform over the entire
one-excitation sector is also invariant and still linear for equal spacing.
At one excitation a rail switch is possible iff the marker is on the current
lane or in a cell of the current petal, provided at least two petals are live.
All others are trapped. With K=sum_i(n_i-1) over live petals, the active
fraction of the uniform one-excitation sector for equal spacing is
sum_i n_i² / ((sum_i n_i)*(1+K)). At an arbitrary clock tick, restricting to
that invariant active sector gives square rail weights. In fact there are two
active cycles (one per direction); either gives that same long-time profile
from ANY of its initial phases. This is not a claim about the first tick from
a nonstationary preparation. At handoff instants each rail occurs equally
often. No preparation law, entropy law, independent
clicks or fair initial microstate distribution is derived. Multiple petals
and the observational ability to follow a labelled cursor are detector inputs.
Reversibility concerns the installed detector, NOT signed folding/installation.

Run: python3 -B -O -m scripts.probe_reversible_excitation_detector
"""

from collections import Counter, deque
from fractions import Fraction
from itertools import pairwise, permutations, product
from math import lcm

from scripts.probe_bipartite_triangle_origin import need
from scripts.probe_reciprocal_detector_petals import unary
from scripts.probe_unary_first_passage_detector import (
    NoLiveRail,
    exclusive_children,
    raw,
)


class Apparatus:
    def __init__(self, sizes, order=None, lengths=None):
        self.sizes = tuple(sizes)
        need(all(n >= 0 for n in sizes), "negative petal")
        live = tuple(i for i,n in enumerate(sizes) if n)
        if not live:
            raise NoLiveRail("no positive-length petal")
        self.order = live if order is None else tuple(order)
        need(sorted(self.order) == sorted(live), "wrong hub order")
        self.adj, self.arc = [[]], {}
        self.hub, self.starts, self.cells = {}, {}, {}
        self.cellmask = [0]*len(sizes)
        self.perimeter = [0]*len(sizes)
        for i in live:
            n = sizes[i]
            junction = [0, *(self.new() for _ in range(n-1)), 0]
            ports = {v:{} for v in junction[1:-1]}
            for k in range(n):
                length = 4 if lengths is None else lengths[i][k]
                need(length >= 4 and length % 2 == 0, "need simple even wire")
                self.perimeter[i] += length
                for b in (0,1):
                    path = [junction[k], *(self.new() for _ in range(length-1)), junction[k+1]]
                    for v,w in pairwise(path):
                        need(v != w and (v,w) not in self.arc, "non-simple edge")
                        self.adj[v].append(w)
                        self.adj[w].append(v)
                        self.arc[v,w] = self.arc[w,v] = (i,b)
                    if k == 0:
                        self.starts[i,1,b] = path[1]
                    else:
                        ports[path[0]][1,b] = path[1]
                    if k+1 == n:
                        self.starts[i,-1,b] = path[-2]
                    else:
                        ports[path[-1]][-1,b] = path[-2]
            for v,p in ports.items():
                bit = 1 << len(self.cells)
                self.cellmask[i] |= bit
                self.cells[v] = (bit, p, {neighbor:key for key,neighbor in p.items()})
        for j,i in enumerate(self.order):
            for d,b in product((1,-1),(0,1)):
                new_i = self.order[(j+d*b) % len(self.order)]
                self.hub[self.starts[i,-d,b]] = self.starts[new_i,d,b]
        self.audit_local()

    def new(self):
        self.adj.append([])
        return len(self.adj)-1

    def scatter(self, v, ingress, mask):
        if v == 0:
            return self.hub[ingress], mask
        if v in self.cells:
            bit, ports, name = self.cells[v]
            side, lane = name[ingress]
            stored = int(bool(bit & mask))
            return ports[-side,stored], (mask | bit) if lane else (mask & ~bit)
        a,b = self.adj[v]
        need(ingress in (a,b), "non-incident wire ingress")
        return b if ingress == a else a, mask

    def step(self, state):
        u,v,mask = state
        w,newmask = self.scatter(v,u,mask)
        return v,w,newmask

    def inverse(self, state):
        u,v,mask = state
        w,oldmask = self.scatter(u,v,mask)
        return w,u,oldmask

    def launch(self, rail, direction, mask):
        return 0,self.starts[rail,direction,1],mask

    def audit_local(self):
        color, todo = {0:0}, deque([0])
        while todo:
            v = todo.popleft()
            need(len(set(self.adj[v])) == len(self.adj[v]), "not a simple graph")
            local = (0,self.cells[v][0]) if v in self.cells else (0,)
            for p in self.adj[v]:
                need(v in self.adj[p] and self.arc[v,p] == self.arc[p,v], "asymmetric edge")
                if p not in color:
                    color[p] = 1-color[v]
                    todo.append(p)
                need(color[p] != color[v], "not bipartite")
                for m in local:
                    w,t = self.scatter(v,p,m)
                    need(w in self.adj[v] and self.scatter(v,w,t) == (p,m),
                         "local scatter not an involution on its full domain")
        need(len(color) == len(self.adj), "disconnected")


def periodic_census(g, start):
    # Measure by actual return; no target weights or ticket list in the walk.
    counts, handoffs, state = Counter(), Counter(), start
    for _ in range(200000):
        i,b = g.arc[state[:2]]
        counts[i] += 1
        if state[0] == 0 and b == 1:
            handoffs[i] += 1
        state = g.step(state)
        if state == start:
            return counts,handoffs
    raise AssertionError("no complete return within monitor budget")


def family(g, mask, direction, first):
    q = {i:1+(mask & g.cellmask[i]).bit_count() for i in g.order}
    multiples = lcm(*q.values())
    start = g.launch(first,direction,mask)
    counts,visits = periodic_census(g,start)
    # A rotationally symmetric marked word can have a smaller exact period
    # than the L-tour restoration guaranteed by the gap argument.
    turns = visits[first]
    need(turns > 0 and multiples % turns == 0 and
         all(visits[i] == turns and counts[i]*q[i] == turns*g.sizes[i]*g.perimeter[i]
             for i in g.order), "gap law on full microstate return")
    return counts


def ensembles(g):
    K = len(g.cells)
    states = {(u,v,m) for u,v in g.arc for m in range(1 << K)}
    need({g.step(s) for s in states} == states, "global map not a permutation")
    all_counts,one,active,hands = Counter(),Counter(),Counter(),Counter()
    eligible_states = set()
    for s in states:
        u,v,m = s
        t = g.step(s)
        i,b = g.arc[u,v]
        j,c = g.arc[t[:2]]
        need(g.inverse(t) == s and g.step(g.inverse(s)) == s, "global inverse")
        need(b+m.bit_count() == c+t[2].bit_count(), "excitation number changed")
        all_counts[i] += 1
        if b+m.bit_count() != 1:
            continue
        one[i] += 1
        eligible = bool(b or (m & g.cellmask[i]))
        need(eligible == bool(c or (t[2] & g.cellmask[j])), "activity not invariant")
        if eligible:
            active[i] += 1
            eligible_states.add(s)
        if u == 0 and b:
            hands[i] += 1
        # Start from every arc in both directions, including mid-wire origins.
        work = s
        if len(g.order) > 1 and eligible:
            for _ in range(g.sizes[i]*g.perimeter[i]):
                work = g.step(work)
                if g.arc[work[:2]][0] != i:
                    break
            else:
                raise AssertionError("active state failed bounded distinct-port herald")
        elif not eligible:
            for _ in range(g.perimeter[i]):
                work = g.step(work)
                need(g.arc[work[:2]][0] == i, "external marker reached a trapped cursor")
            need(work == s, "trap did not close")
        else:
            need(len(g.order) == 1 and j == i, "one rail has no distinct-port herald")
    for i in g.order:
        p = g.perimeter[i]
        need((all_counts[i],one[i],active[i],hands[i]) ==
             (4*p*(1 << K),2*p*(1+K),2*p*g.sizes[i],2), "wrong time/handoff measures")
    # Do not assume a uniform initial phase. Identify the two entire active
    # orbits from actual hops and show there are no other eligible states.
    for direction in (1,-1):
        start = work = g.launch(g.order[0],direction,0)
        local = Counter()
        while work in eligible_states:
            eligible_states.remove(work)
            local[g.arc[work[:2]][0]] += 1
            work = g.step(work)
        need(work == start and all(local[i] == g.perimeter[i]*g.sizes[i] for i in g.order),
             "active orientation cycle changed")
    need(not eligible_states, "eligible states outside the two active cycles")
    return len(states),sum(one.values()),sum(active.values())


def main():
    sizes = unary(4, (*raw((2,1,-3)), (3,1), (3,-1)))
    need(sizes == (2,1,3,0), "signed quotient changed")
    uniform = (768,192,112)
    for order in permutations((0,1,2)):
        g = Apparatus(sizes, order)
        need(ensembles(g) == uniform, "primary ensemble counts")
        for first,direction,mask in product(order,(1,-1),range(8)):
            counts = family(g,mask,direction,first)
            if mask == 0:
                need(counts == {0:16,1:4,2:36}, "one-mark square")
            if mask == 7:
                need(counts == {0:8,1:4,2:12}, "filled-register linear control")
    need(Fraction(uniform[2],uniform[1]) == Fraction(7,12), "wrong primary active fraction")
    patterns = 0
    for ns in product(range(1,5), repeat=3):
        g = Apparatus(ns)
        for mask in range(1 << len(g.cells)):
            family(g,mask,1,0)
            patterns += 1
    for ns in ((1,), (2,), (3,), (1,1), (3,3), (2,2,2)):
        ensembles(Apparatus(ns))
    # Gap rotation uses every edge per lap: reordering lengths within a
    # petal has no effect, unlike the root-reflecting first-passage device.
    for widths in ((4,6,8), (6,6,6), (8,6,4)):
        g = Apparatus((3,2), lengths=(widths,(4,4)))
        need(family(g,0,1,0) == family(g,0,-1,1) == {0:54,1:16}, "wire-order control")
        ensembles(g)
    native = Apparatus(unary(10, exclusive_children((2,1,-3))))
    raw_counts = family(native,0,1,0)
    registers = tuple(sum(raw_counts[j] for j in range(3*i,3*i+3)) for i in range(3))
    need(registers == (96,24,216) and raw_counts[9] == 0 and sum(raw_counts.values()) == 336,
         "native exclusive register clock")
    try:
        Apparatus((0,0))
    except NoLiveRail:
        pass
    else:
        raise AssertionError("no excitation channel on a dark packet")
    print(f"full local involutions; {patterns} marked-cell preparations; every hop is a physical edge")
    print("(2,1,-3): 16/4/36 ticks; filled registers 8/4/12; native exclusive 96/24/216")
    print("768 global states; 192 one-marker, 112 active (7/12); timed active 32/8/72; handoffs 2/2/2")
    print("uniform unconditioned measures linear; no assumption that a preparation samples them")


if __name__ == "__main__":
    main()
