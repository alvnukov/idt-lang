"""A local clocked detector on a simple undirected bipartite apparatus graph.

For n unary cells, identify both ends of the logical chain with the same hub.
Replace each logical edge by four physical edges with fresh private internal
vertices. Even the logical one-edge loop has *different* physical hub ports;
parallel logical edges also have disjoint wires. Each two-port wire relay
exits opposite its ingress. Interior chain switches alternate ports. The hub
reflects first-port returns back along that same edge; a last-port return
dispatches into the next nonempty petal, on the next (counted) physical hop.
Every tick is one adjacent hop with the traversed edge's detector label.

The previous unary first-passage calculation now counts physical time times
four; there is no unscored wire latency or cursor reset. The event source is
still a trigger clock, not iid particles. Supplied: preparation and signed
cancellation/folding into anonymous unary cells; a distinguished common hub,
labelled petals and oriented ports, fixed local successor wiring, equal wire
lengths, switch/pass-through node roles, persistent cursor and switches.
Reciprocal *adjacency* is not a reversible or anonymous scattering rule: the
hub can send two different ingresses to the same port. Opposite directions
on an undirected edge incur the same cost. Empty rails have no physical port;
the all-dark packet cannot accept a trigger. No input occurrence is selected.

Control: a fair ordinary rotor at JUST the hub makes all logical junctions
ordinary rotors, leaving wire relays untouched. On any recurrent period let
m_v count outgoing traversals of each logical port at v: they are equal there
because the rotor returns to its phase. Flux balance makes m_v the average
of m_u on incident ports (counting multiple edges and both ends of a loop).
On a finite connected graph the maximum principle gives all m_v equal. Each
wire then costs its length in each direction: stock follows physical edge
count, linear in n for equal wire lengths. The argument applies directly on
the physical graph if EVERY vertex is an ordinary rotor. A finite trajectory
is eventually periodic in both cases; this is not a statement about transient
prefixes or about all possible local apparatus.

Run: python3 -B -O -m scripts.probe_reciprocal_detector_petals
"""

from collections import Counter, deque
from itertools import pairwise, product

from scripts.probe_bipartite_triangle_origin import need
from scripts.probe_unary_first_passage_detector import (
    NoLiveRail,
    exclusive_children,
    raw,
)


def unary(port_count, events):
    cells = [[] for _ in range(port_count)]
    for i, sign in events:
        need(0 <= i < port_count and sign in (-1, 1), "invalid occurrence")
        chain = cells[i]
        if chain and chain[-1] != sign:
            chain.pop()
        else:
            chain.append(sign)
    return tuple(map(len, cells))


class Petals:
    def __init__(self, sizes, spacing=None):
        self.adj = [[]]  # Vertex 0 is the common hub.
        self.label = {}
        self.switch = {}
        self.scatter = {}
        self.width = len(sizes)
        ends = []
        for i, n in enumerate(sizes):
            need(n >= 0, "negative size")
            if not n:
                continue
            junctions = [0, *(self.new() for _ in range(n-1)), 0]
            arrivals, departures = [], []
            for k in range(n):
                length = 4 if spacing is None else spacing[i][k]
                need(length >= 4 and length % 2 == 0, "need simple, even wires")
                wire = [junctions[k], *(self.new() for _ in range(length-1)), junctions[k+1]]
                departures.append(wire[1])
                arrivals.append(wire[-2])
                for a, b in pairwise(wire):
                    need(a != b and (a,b) not in self.label, "non-simple physical edge")
                    self.adj[a].append(b)
                    self.adj[b].append(a)
                    self.label[a,b] = self.label[b,a] = i
            for j in range(1, n):
                self.switch[junctions[j]] = (arrivals[j-1], departures[j])
            ends.append((departures[0], arrivals[-1]))
        if not ends:
            raise NoLiveRail("no petal can accept a trigger")
        for j, (first, last) in enumerate(ends):
            self.scatter[first] = first
            self.scatter[last] = ends[(j+1) % len(ends)][0]
        self.start = ends[0][0]
        self.boundary_port = ends[-1][1]  # Passive cycle monitor, not a clock.
        self.audit()

    def new(self):
        self.adj.append([])
        return len(self.adj)-1

    def audit(self):
        need(set(self.scatter) == set(self.adj[0]), "unwired or duplicate hub port")
        color, q = {0:0}, deque([0])
        while q:
            v = q.popleft()
            ns = self.adj[v]
            need(len(set(ns)) == len(ns) and v not in ns, "loop/parallel edge")
            need(v == 0 or len(ns) == 2, "ill-formed degree")
            for w in ns:
                need(v in self.adj[w] and self.label[v,w] == self.label[w,v], "not reciprocal")
                if w not in color:
                    color[w] = 1-color[v]
                    q.append(w)
                need(color[w] != color[v], "odd cycle")
        need(len(color) == len(self.adj), "disconnected apparatus")


class Walker:
    def __init__(self, graph, mode="ingress", bits=()):
        need(mode in ("ingress", "neutral-hub", "all-rotor"), "unknown node rules")
        self.g, self.mode = graph, mode
        self.prev, self.v = -1, 0
        self.phase = [0]*len(graph.adj)
        if bits:
            need(len(bits) == len(graph.switch), "wrong number of switch bits")
            for v, bit in zip(graph.switch, bits, strict=True):
                self.phase[v] = int(bit)

    def hop(self):
        g, v, p = self.g, self.v, self.prev
        if v == 0 and self.mode == "ingress":
            w = g.start if p == -1 else g.scatter[p]
        elif self.mode == "all-rotor" or v == 0 or v in g.switch:
            ports = g.switch[v] if v in g.switch else g.adj[v]
            w = ports[self.phase[v]]
            self.phase[v] = (self.phase[v]+1) % len(ports)
        else:
            a, b = g.adj[v]
            need(p in (a,b), "wire has no ingress")
            w = b if a == p else a
        self.prev, self.v = v, w
        # Lookup in the symmetric physical edge table; no virtual transitions.
        return g.label[v,w], v == g.boundary_port and w == 0

    def state(self):
        return self.prev, self.v, tuple(self.phase)


def block(walk):
    counts = Counter()
    for _ in range(10000):  # monitor timeout only; stop on observed last arrival
        rail, completed = walk.hop()
        counts[rail] += 1
        if completed:
            return tuple(counts[i] for i in range(walk.g.width))
    raise AssertionError("timed out before physical return")


def recurrent(walk):
    seen = set()
    for _ in range(20000):
        state = walk.state()
        if state in seen:
            break
        seen.add(state)
        walk.hop()
    else:
        raise AssertionError("recurrent state not reached within test budget")
    start, edges, counts = walk.state(), Counter(), Counter()
    for _ in range(20000):
        rail, _ = walk.hop()
        edges[walk.prev, walk.v] += 1
        counts[rail] += 1
        if walk.state() == start:
            break
    else:
        raise AssertionError("period not closed")
    need(set(edges) == set(walk.g.label) and len(set(edges.values())) == 1,
         "unequal directed edge use on recurrent orbit")
    return tuple(counts[i] for i in range(walk.g.width))


def main():
    phases = 0
    for n in range(1, 11):
        g = Petals((n,))
        need(len(g.label) == 8*n and len(g.adj) == 4*n, "wrong simple cycle")
        for bits in product((False,True), repeat=n-1):
            walk = Walker(g, bits=bits)
            correction = 2*sum(j for j,b in enumerate(bits, 1) if b)
            need(block(walk) == (4*(n*n-correction),), "first passage clock")
            need(not any(walk.phase[v] for v in g.switch), "phase not restored")
            need(block(walk) == (4*n*n,), "future passage clock")
            phases += 1
    v = (2,1,-3)
    noisy = (*raw(v), (1,-1), (1,1), (3,-1), (3,1))
    g = Petals(unary(4, reversed(noisy)))
    walk = Walker(g)
    need(block(walk) == block(walk) == (16,4,36,0), "mixed nonempty/dark clock")
    for mode in ("neutral-hub", "all-rotor"):
        walk = Walker(g, mode)
        for j in range(6):
            walk.phase[0] = j  # vary hub's initial port on a fresh trajectory
            counts = recurrent(walk)
            need(counts[1] > 0 and counts == (2*counts[1],counts[1],3*counts[1],0),
                 "ordinary rotor did not yield linear frequencies")
            walk = Walker(g, mode)
    exclusive = block(Walker(Petals(unary(10, exclusive_children(v)))))
    registers = tuple(sum(exclusive[3*i:3*i+3]) for i in range(3))
    need(registers == (96,24,216) and sum(exclusive) == 336 and exclusive[-1] == 0,
         "native register clock")
    # Same physical edge count and logical size, different early/late wire cost.
    costs = []
    for lengths in ((4,6,8), (6,6,6), (8,6,4)):
        g = Petals((3,), spacing=(lengths,))
        need(len(g.label) == 36, "unequal size timing comparison")
        costs.append(block(Walker(g))[0])
    need(costs == [46,54,62], "nonuniform subdivision timing control")
    try:
        Petals(unary(1, ((0,1),(0,-1))))
    except NoLiveRail:
        pass
    else:
        raise AssertionError("dark packet incorrectly accepted")
    print(f"{phases} switch patterns; simple reciprocal petals, one adjacent hop per clock tick")
    print("(2,1,-3): (16,4,36) ticks; neutral hub and ordinary rotors -> linear 2:1:3")
    print(f"exclusive registers {registers}, 336/336 ticks; equal-edge-count clock control {costs}")


if __name__ == "__main__":
    main()
