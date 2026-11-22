"""Unoriented occurrence graphs: a finite triangle carrier, not a QM derivation.

A packet has only anonymous vertices, symmetric adjacency and a rail tag per
vertex. There is no stored bipartition, sign, directed edge or amplitude. On a
connected bipartite graph every path between two vertices has the same parity:
two paths of different parity would give an odd closed walk. A temporary BFS
root only names the two parity classes; changing it can just interchange them.
This recovers the content of a relative two-role sign, not its physical origin.

Supplied: connected bipartite packets (with an edge for the two-sheet device),
rail identities, coherent attachment of an exchanged copy, the Cartesian
product with ordered rail pairs, and cancellation plus ordered-pair readout.
The triangle device also supplies its three tags, swaps and distinguished
output ports. The readout is destructive if performed: predictions at later
stages use the full unmeasured branch graph, not a survivors-only graph.
Branch counts are populations, not trajectories of persistent event tickets.
Joint readout can compare occurrences on the same paired rail; not a Bell-local
detector construction. No coordinates, odd-cycle physics or universal proof.

Run: python3 -B -O -m scripts.probe_bipartite_triangle_origin
"""

from collections import defaultdict, deque
from dataclasses import dataclass
from functools import cache
from itertools import combinations, permutations, product


def need(condition, message):
    if not condition:
        raise AssertionError(message)


class OutsideCarrier(ValueError):
    """No connected bipartite path-parity relation on this input."""


@dataclass(frozen=True)
class Packet:
    tags: tuple
    adj: tuple  # one frozenset of neighbors per occurrence; indices are just names


def graph(tags, edges):
    tags = tuple(tags)
    adj = [set() for _ in tags]
    for u, v in edges:
        adj[u].add(v)
        adj[v].add(u)
    return Packet(tags, tuple(map(frozenset, adj)))


def edges(g):
    return tuple((u, v) for u, ns in enumerate(g.adj) for v in ns if u <= v)


def path_parity(g, root):
    # This naming is confined to detection/validation. The devices below
    # operate on adjacency and never copy, select or align named colors.
    parity = {root: 0}
    queue = deque([root])
    while queue:
        u = queue.popleft()
        for v in g.adj[u]:
            if v not in parity:
                parity[v] = parity[u] ^ 1
                queue.append(v)
            elif parity[v] == parity[u]:
                raise OutsideCarrier("odd cycle")
    if len(parity) != len(g.tags):
        raise OutsideCarrier("disconnected")
    return parity


def stock(g, root=0, reverse_pairing=False):
    # A port may cross off any two opposite occurrences on the same rail.
    # Each step removes one from each class. Terminal cardinality therefore
    # does not depend on which pairs were picked, though survivor identities do.
    sides = path_parity(g, root)
    bins = defaultdict(lambda: ([], []))
    for u, tag in enumerate(g.tags):
        bins[tag][sides[u]].append(u)
    out = {}
    for tag, (a, b) in bins.items():
        if reverse_pairing:
            a.reverse()
            b.reverse()
        while a and b:
            a.pop()
            b.pop()
        live = a or b
        out[tag] = len(live) ** 2  # ordered pairs, including the diagonal
    return out


def mass(g):
    return sum(stock(g).values())


def attach(g, exchange, cross):
    n = len(g.tags)
    same = edges(g)
    return graph(g.tags + tuple(map(exchange, g.tags)),
                 (*same, *((u+n, v+n) for u, v in same),
                  *((u, v+n) for u, v in cross)))


def split(g, exchange):
    # Positive port: cross to neighbors in the other sheet. Negative port:
    # cross to the corresponding vertex. Connected sheets with >=1 edge
    # stay connected. On the first wiring corresponding vertices are two
    # steps apart; on the second they are one step apart.
    need(any(g.adj), "two-sheet device needs a connected packet with an edge")
    return (attach(g, exchange, ((u, v) for u, ns in enumerate(g.adj) for v in ns)),
            attach(g, exchange, ((u, u) for u in range(len(g.tags)))))


def independent(g, h):
    # Ordinary unoriented Cartesian graph product: each edge changes just one
    # occurrence. The parity of any product path is the XOR of its two projected
    # path parities (ignoring stationary steps). No input frame is chosen.
    n = len(h.tags)
    return graph(product(g.tags, h.tags),
                 (*((u*n+j, v*n+j) for u, v in edges(g) for j in range(n)),
                  *((i*n+u, i*n+v) for i in range(len(g.tags)) for u, v in edges(h))))


def rename(g, order):
    dest = {old: new for new, old in enumerate(order)}
    return graph((g.tags[u] for u in order), ((dest[u], dest[v]) for u,v in edges(g)))


D = range(3)
RAYS = ((0, 0), (2, 1), (1, 0), (0, 1), (2, 0), (1, 1))


def seed(k):
    return graph(((k+1) % 3, (k+2) % 3), [(0, 1)])


def reflection(k, x):
    # Fix k and exchange the other two anonymous tags. Arithmetic enumerates
    # the three possible transpositions; distances and angles never enter.
    return (2*k-x) % 3


def single_probe():
    prepared = {}
    for k in D:
        ports = split(seed((k+1) % 3), lambda x: reflection(k, x))
        need(tuple(map(mass, ports)) == (6, 2), "single prep raw stocks")
        for b, g in enumerate(ports):
            prepared[k, b] = g
    first = (4, 3, 1, 0, 1, 3)
    for i, prep in enumerate(RAYS):
        g = prepared[prep]
        for j, (k, b) in enumerate(RAYS):
            ports = split(g, lambda x: reflection(k, x))
            hits = tuple(map(mass, ports))
            need(sum(hits) == 4*mass(g), "unconditioned read stock")
            need(hits[b] == mass(g)*first[(j-i) % 6], "cyclic single read")
    return prepared


def joint_probe():
    for a, b in product(D, repeat=2):
        g = independent(seed(a), seed(b))
        need(len(g.tags) == 4 and len(edges(g)) == 4 and mass(g) == 4,
             "unit checkerboard scale")
        ports = split(g, lambda t: (t[1], t[0]))
        flags = tuple(map(mass, ports))
        need(flags == ((16, 0) if a == b else (10, 6)), "joint herald stock")
        for k, l in product(D, repeat=2):
            left = lambda t: (reflection(k, t[0]), t[1])
            right = lambda t: (t[0], reflection(l, t[1]))
            for branch, h in enumerate(ports):
                ab = [stock(q) for p in split(h, left) for q in split(p, right)]
                ba = [stock(q) for p in split(h, right) for q in split(p, left)]
                need(ab == [ba[n] for n in (0, 2, 1, 3)], "order by paired rail")
                raw = tuple(sum(s.values()) for s in ab)
                need(sum(raw) == 16*flags[branch], "all issued rows by herald")
                if branch and a != b:
                    need(raw == ((0,48,48,0) if k == l else (36,12,12,36)),
                         "antisymmetric conditional table")


def small_graphs():
    # Exhaust every simple graph on 2..4 named occurrences and every assignment
    # of two rail tags, filtering to this carrier. Signed differences below
    # are solely the independent algebraic check; no device receives one.
    count = 0
    for n in range(2, 5):
        possible = tuple(combinations(range(n), 2))
        for mask in range(1 << len(possible)):
            wires = [p for i, p in enumerate(possible) if mask & (1 << i)]
            topology = graph(range(n), wires)
            try:
                parts = path_parity(topology, 0)
            except OutsideCarrier:
                continue
            for tags in product(range(2), repeat=n):
                g = Packet(tags, topology.adj)
                response = tuple(sum((1 if parts[u] else -1)
                                     for u in range(n) if tags[u] == k)
                                 for k in range(2))
                for swap in (False, True):
                    def exchange(k):
                        return 1-k if swap else k
                    for port, h in enumerate(split(g, exchange)):
                        observed = stock(h)
                        expected = tuple((response[k] + (1,-1)[port]*response[exchange(k)])**2
                                         for k in range(2))
                        need(tuple(observed.get(k, 0) for k in range(2)) == expected,
                             "two-sheet effect on small graph")
                        # Each connected input sheet already fixes its internal
                        # relative roles. Any single allowed cross-link suffices
                        # for this readout, but is not the same graph/device.
                        for u in range(n):
                            for v in ((u,) if port else g.adj[u]):
                                need(stock(attach(g, exchange, [(u,v)])) == observed,
                                     "relative role depends on choice of allowed anchor")
                count += 1
    need(count == 332, "small-graph coverage")
    return count


def controls(prepared):
    small_graphs()
    # A rail with four against two offers 24 possible ordered pairing
    # sequences, six distinct survivor sets, one terminal read stock.
    g = graph((0,)*6, product(range(4), (4, 5)))
    par = path_parity(g, 0)

    @cache
    def terminals(live):
        choices = [(u,v) for u,v in combinations(live, 2) if par[u] != par[v]]
        if not choices:
            return (live,)
        return tuple(row for u,v in choices for row in terminals(live - {u,v}))

    ends = terminals(frozenset(range(6)))
    need(len(ends) == 24 and len(set(ends)) == 6 and
         {len(list(product(s, repeat=2))) for s in ends} == {4}, "pairing histories")
    for g in prepared.values():
        for order in permutations(range(len(g.tags))):
            h = rename(g, order)
            for r in range(len(h.tags)):
                need(stock(h, r, True) == stock(g), "anonymous parity detection")
            for k in D:
                p = lambda x: reflection(k, x)
                need(tuple(map(stock, split(h,p))) == tuple(map(stock, split(g,p))),
                     "device changed under occurrence renaming")
    for g,h in product(prepared.values(), repeat=2):
        gs,hs = stock(g),stock(h)
        expect = {(a,b): x*y for a,x in gs.items() for b,y in hs.items()}
        need(stock(independent(g,h)) == expect, "product stock not unit scale")
    # The two sheets are literally the same two original tagged edges in both
    # worlds; only a subsequently installed cross-edge differs. Marginals
    # (induced before/after fusion) cannot choose that wiring.
    two = graph((0,1,0,1), [(0,1),(2,3)])
    results = []
    for bridge in ((0,3), (0,2)):
        fused = graph(two.tags, (*edges(two), bridge))
        need(set(edges(fused)) - {bridge} == set(edges(two)), "changed an input")
        results.append(stock(fused))
    need(results == [{0:4, 1:4}, {0:0, 1:0}], "fusion ambiguity")
    for g, why in ((two, "disconnected"), (graph((0,1,2), [(0,1),(1,2),(2,0)]),
                                            "odd cycle")):
        try:
            stock(g)
        except OutsideCarrier as exc:
            need(str(exc) == why, "wrong carrier boundary")
        else:
            raise AssertionError("out-of-model graph classified as a valid packet")
    # Cancelling two middle vertices would disconnect the two still-live
    # endpoints, forgetting their odd separation. Cancellation is a readout,
    # not a graph rewrite carried into the next device.
    path = graph((0,2,2,1), [(0,1),(1,2),(2,3)])
    need(stock(path) == {0:1, 2:0, 1:1} and path_parity(path,0)[3] == 1 and
         (0,3) not in edges(path), "deletion control")


def main():
    prepared = single_probe()
    joint_probe()
    controls(prepared)
    print("Unoriented K2 seed; preparation stocks 6,2. All 36 single reads: "
          "cyclic (4,3,1,0,1,3)/4.")
    print("Unit-scale Cartesian square. All 9 input pairs x 9 settings, both orders: "
          "distinct-edge heralds 10,6 of 16; equal edges 16,0. Distinct antisymmetric "
          "raw cells (0,48,48,0) / (36,12,12,36), 96 of 256 final events.")
    print("Same two disconnected inputs: alternative bridge gives total 8 or 0. "
          "Odd cycle outside this carrier. Readout does not erase later wiring.")


if __name__ == "__main__":
    main()
