"""Integer occupancy at reciprocal loop cells, not intrinsically marked particles.

There is one moving packet of k>=1 indistinguishable units; a cell can hold
any s>=0 parked units. Forward 1+s and park k-1. This exchanges the moving
excess k-1 with local stock, so it conserves units and is an involution.
The opposite port is supplied. No labelled unit is permanently "the cursor".
Zero parked stock requires no material register token; it still represents
an available location. Geometry, port orientation, grouping/co-motion of a
packet, a time step and distinguishable cargo-sensitive hub ports are inputs.

With two units, empty sites and a moving pair, every logical lap rotates one
excess through n slots (n-1 cells and the packet). At the hub a singleton
continues its petal; k>1 switches to the next one. It takes n laps of n hops
to reunite the pair at the hub. This counts ONE occupied packet crossing per
tick: the pair crosses each logical bond once, so unit flux is n²+n, not n².
Equal physical subdivision scales both counts. Parked units outside the
current petal can trap a singleton; one unit cannot hand off. These are
prepared-clock observations, not single-shot probabilities or material motion.

Uniqueness under a separate response premise: let the exiting mobile load
be F(s), independent of k. Conservation and positivity give F(0)=1 on (1,0).
Then (k,0)->(1,k-1); involution forces F(k-1)=k for every k>=1.
Without independence, a cold split and its inverse constrain only the two
extremes on each fixed-total row. For total >=4 interior permutations can
differ. Both-positive interior states must map to the interior under ANY
such involution, since the two extremes already map onto one another. Thus
even arbitrary many units cannot discriminate these alternatives by a mere
bound/singleton threshold on this apparatus. Local load counts can. No
hard-core constraint, quantum statistics or proof-status change is inferred.

A separate reciprocal reporting station can convert one arriving bunch into
one unit crossing on a designated reporting link WITHOUT consuming that unit.
Use two further ports and a four-edge return loop. First exchange at the
station, circle the loop, exchange again, then leave on the onward port.
With initially empty stock exactly one unit circles; with stock s it is 1+s.
The original loads are restored after four extra timed hops. This is an
optional instrument with supplied port wiring and a passive unit counter.
It is not installed remotely throughout the original mesh or delivered to
a common detector; destructive absorption would prevent the second contact.

Run: python3 -B -O -m scripts.probe_indistinguishable_mobile_load
"""

from collections import Counter
from itertools import pairwise, product

from scripts.probe_bipartite_triangle_origin import need
from scripts.probe_reversible_cell_census import TablePetal, inferred_rule, involutions


def exchange(k, s):
    return 1 + s, k - 1


def extremes_only(k, s):
    return exchange(k, s) if k == 1 or s == 0 else (k, s)


class Site:
    def __init__(self, stores=False):
        self.stores = stores
        self.ports = []
        self.through, self.marked = {}, {}


class Port:
    def __init__(self, at, i, j, direction):
        self.at, self.name = at, (i, j, direction)
        at.ports.append(self)
        self.peer = None


class Mesh:
    def __init__(self, sizes, subdivision):
        need(
            all(n >= 0 for n in sizes) and any(sizes) and subdivision >= 1,
            "invalid mesh",
        )
        self.hub = Site()
        self.cells, self.index, self.ends = [], {}, {}
        self.order = [i for i, n in enumerate(sizes) if n]
        for i in self.order:
            N = sizes[i] * subdivision
            path = [self.hub]
            for j in range(1, N):
                s = Site(j % subdivision == 0)
                path.append(s)
                if s.stores:
                    self.cells.append(s)
            path.append(self.hub)
            for j in range(N):
                a, b = Port(path[j], i, j, 1), Port(path[j + 1], i, j, -1)
                a.peer, b.peer = b, a
                self.index[a.name], self.index[b.name] = a, b  # diagnostics/launch only
            self.ends[i, 1] = self.index[i, 0, 1]
            self.ends[i, -1] = self.index[i, N - 1, -1]
            for site in path[1:-1]:
                a, b = site.ports
                site.through = {a: b, b: a}
        for j, i in enumerate(self.order):
            for d in (-1, 1):
                arrival = self.ends[i, -d]
                self.hub.through[arrival] = self.ends[i, d]
                other = self.order[(j + d) % len(self.order)]
                self.hub.marked[arrival] = self.ends[other, d]
        for p in self.hub.ports:
            need(
                self.hub.through[self.hub.through[p]] is p
                and self.hub.marked[self.hub.marked[p]] is p,
                "hub rule is not reciprocal",
            )


class Walk:
    def __init__(self, port, moving, parked=(), rule=exchange):
        self.port, self.k, self.parked, self.rule = port, moving, dict(parked), rule
        need(
            moving >= 1 and all(v.stores and s > 0 for v, s in self.parked.items()),
            "invalid prepared load",
        )

    def tick(self):
        # No mesh, sizes, global totals, IDs or remote sites are consulted.
        old, flow = self.port, self.k
        arrival = old.peer
        node = arrival.at
        if node.stores:
            self.k, stock = self.rule(self.k, self.parked.get(node, 0))
            if stock:
                self.parked[node] = stock
            else:
                self.parked.pop(node, None)
        ports = node.marked if node.marked and self.k > 1 else node.through
        self.port = ports[arrival]
        return old.name[0], flow  # passive tag and unlabelled unit flux on THIS edge

    def state(self):
        return self.port, self.k, frozenset(self.parked.items())


def cycle(walk):
    start = walk.state()
    visits, flux = Counter(), Counter()
    for _ in range(100000):
        i, k = walk.tick()
        visits[i] += 1
        flux[i] += k
        if walk.state() == start:
            return visits, flux
    raise AssertionError("no complete state return within budget")


def projection(g, mesh, sizes):
    # Collapse the old zero/one lanes onto ONE channel in the occupancy
    # implementation. Only this independent comparison uses old bit names.
    arcs, sites = {}, {}
    for i in mesh.order:
        for b in (0, 1):
            u, v = 0, g.starts[i, 1, b]
            for j in range(4 * sizes[i]):
                physical = mesh.index[i, j, 1]
                arcs[u, v], arcs[v, u] = physical, physical.peer
                if v == 0:
                    need(j + 1 == 4 * sizes[i], "premature hub")
                    break
                if v in g.cells:
                    bit, ports, _ = g.cells[v]
                    sites[bit] = physical.peer.at
                    w = ports[1, b]
                else:
                    x, y = g.adj[v]
                    w = y if x == u else x
                u, v = v, w
    need(
        set(arcs) == set(g.arc) and set(sites.values()) == set(mesh.cells),
        "incomplete lane-to-occupancy projection",
    )

    def decode(state):
        u, v, mask = state
        parked = frozenset((site, 1) for bit, site in sites.items() if mask & bit)
        return arcs[u, v], 1 + g.arc[u, v][1], parked

    return decode


def compare_all_two(sizes):
    mesh = Mesh(sizes, 4)
    g = TablePetal(
        sizes, inferred_rule(False, False)
    )  # transmitting swap, not the other fits
    decode = projection(g, mesh, sizes)
    states, active = set(), set()
    for u, v in g.arc:
        for mask in range(1 << len(g.cells)):
            if g.arc[u, v][1] + mask.bit_count() != 1:
                continue
            old = (u, v, mask)
            new = decode(old)
            walk = Walk(*new)
            states.add(new)
            if walk.k == 2 or mask & g.cellmask[g.arc[u, v][0]]:
                active.add(new)
            walk.tick()
            need(
                walk.state() == decode(g.step(old)),
                "one physical tick differs from TablePetal",
            )
            need(walk.k + sum(walk.parked.values()) == 2, "two-unit conservation")
    need(
        len(states) == len(mesh.index) * (1 + len(mesh.cells)),
        "total-two phase space not covered",
    )
    visited = set()
    for d in (-1, 1):
        cur = Walk(mesh.ends[mesh.order[0], d], 2)
        start = cur.state()
        while cur.state() not in visited:
            visited.add(cur.state())
            cur.tick()
        need(cur.state() == start, "orientations merged")
    need(visited == active, "active phases do not exhaust the co-located sector")
    return len(states), len(active)


def collision_controls():
    # On total N label the states by k=1..N. Enumerate all internal
    # involutions after exchanging the two forced extremes at N>=2.
    rows = []
    for N in range(1, 9):
        found = 0
        for interior in involutions(max(0, N - 2)):
            exits = [1] if N == 1 else [N, *(2 + j for j in interior), 1]
            for k, out in enumerate(exits, 1):
                s = N - k
                need(
                    exits[out - 1] == k
                    and ((out > 1), (N - out > 0)) == ((s > 0), (k > 1)),
                    "hidden change in support or involution",
                )
            found += 1
        rows.append(found)
    need(rows[:5] == [1, 1, 1, 2, 4], "wrong first unconstrained row")
    for k, s in product(range(1, 12), range(12)):
        for rule in (exchange, extremes_only):
            a, b = rule(k, s)
            need(
                a >= 1 and b >= 0 and a + b == k + s and rule(a, b) == (k, s),
                "local laws",
            )
        need(
            exchange(k, s)[0] == exchange(1, s)[0],
            "additive outgoing load depends on incoming k",
        )
    mesh = Mesh((2, 1), 1)
    site = mesh.index[0, 0, 1].peer.at
    experiments = [
        Walk(mesh.index[0, 0, 1], 2, ((site, 2),), r) for r in (exchange, extremes_only)
    ]
    for experiment in experiments:
        experiment.tick()
    need(
        [(w.k, w.parked[site]) for w in experiments] == [(3, 1), (2, 2)],
        "prepared load-resolving collision did not distinguish",
    )
    # Different internal masses but identical threshold trajectories.
    left, right = experiments
    for _ in range(100):
        need(
            left.port is right.port
            and (left.k > 1) == (right.k > 1)
            and set(left.parked) == set(right.parked),
            "threshold-only device distinguished loads",
        )
        left.tick()
        right.tick()
    return rows


def reporter(k, s, direction, miswire=False):
    station, left, right = Site(True), Site(), Site()
    relays = [Site() for _ in range(3)]

    def bond(a, b, label, j):
        p, q = Port(a, label, j, 1), Port(b, label, j, -1)
        p.peer, q.peer = q, p
        return p, q

    source, entry = bond(left, station, "main", 0)
    onward, reverse = bond(station, right, "main", 1)
    path = (station, *relays, station)
    wires = [
        bond(a, b, "meter" if j == 1 else "wire", j)
        for j, (a, b) in enumerate(pairwise(path))
    ]
    branch, returning = wires[0][0], wires[-1][1]
    station.through = {
        entry: branch,
        branch: entry,
        returning: onward,
        onward: returning,
    }
    if miswire:
        # Still an involution, but sends a returning pulse back around the
        # reporting loop in reverse rather than forwards to the main output.
        station.through.update({returning: returning, onward: onward})
    for relay in relays:
        a, b = relay.ports
        relay.through = {a: b, b: a}
    for terminal in (left, right):
        p = terminal.ports[0]
        terminal.through = {p: p}
    for v in (station, left, right, *relays):
        need(
            all(v.through[v.through[p]] is p and p.peer.peer is p for p in v.ports),
            "reporter has a nonreciprocal local connection",
        )
    begin, expected_exit = (source, right) if direction == 1 else (reverse, left)
    w = Walk(begin, k, ((station, s),) if s else ())
    units = ticks = 0
    while ticks < 12:
        label, flow = w.tick()
        ticks += 1
        if label == "meter":
            units += flow
        if w.port.at in (left, right):
            return (
                units,
                ticks,
                w.k,
                w.parked.get(station, 0),
                w.port.at is expected_exit,
            )
    raise AssertionError("reporter did not exit")


def reporter_controls():
    for k, s, d in product(range(1, 9), range(5), (-1, 1)):
        need(
            reporter(k, s, d) == (1 + s, 6, k, s, True),
            "equal-time local reporter or reset",
        )
    need(
        reporter(3, 0, 1, True) == (4, 10, 1, 2, False),
        "miswired return did not distinguish",
    )
    # A destructive counter would eat the outbound unit while k-1 remain
    # parked: no returning mobile packet exists to restore the original bunch.
    need(exchange(3, 0) == (1, 2), "absorbing detector control")


def main():
    for n, d in product(range(1, 17), (-1, 1)):
        for spacing in (1, 4):
            mesh = Mesh((n,), spacing)
            hits, flux = cycle(Walk(mesh.ends[0, d], 2))
            need(
                hits == {0: spacing * n * n} and flux == {0: spacing * n * (n + 1)},
                "one-petal return",
            )
    for ns in ((1,), (2,), (3,), (1, 1), (2, 0, 3), (2, 1, 3), (3, 2, 1, 1)):
        states, active = compare_all_two(ns)
        if ns == (2, 1, 3):
            need((states, active) == (192, 112), "primary phase count")
    for spacing in (1, 4):
        m = Mesh((2, 1, 3), spacing)
        hits, flux = cycle(Walk(m.ends[0, 1], 2))
        need(
            [hits[i] for i in m.order] == [spacing * x for x in (4, 1, 9)]
            and [flux[i] for i in m.order] == [spacing * x for x in (6, 2, 12)],
            "clock versus unit flux",
        )
        parked_elsewhere = m.cells[-1]
        stuck = Walk(m.ends[0, 1], 1, ((parked_elsewhere, 1),))
        one = Walk(m.ends[0, 1], 1)
        need(
            cycle(stuck) == cycle(one) == ({0: 2 * spacing}, {0: 2 * spacing}),
            "a singleton spontaneously recruited a remote or nonexistent unit",
        )
    rows = collision_controls()
    reporter_controls()
    print("two identical units; (2,1,3): occupied crossings 4:1:9, unit flux 6:2:12")
    print("192 two-unit states matched one physical hop each; 112 active, 80 trapped")
    print(
        f"admissible cold-split involutions per total 1..8: {rows}; 4-unit outputs (3,1) vs (2,2)"
    )
    print(
        "local four-edge reporting loop: one unit per cold bunch, 1+s if dirty; original load restored"
    )


if __name__ == "__main__":
    main()
