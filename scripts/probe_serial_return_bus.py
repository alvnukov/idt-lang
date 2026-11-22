"""Address-free serial return by a transient mismatch; count crossings, not time.

A tap exchanges moving excess x=k-1 with its stationary stock s. If x=s,
connect A/F and bus-/bus+; otherwise connect A/bus+ and bus-/D. Unpaired
ports reflect. Each port map is an involution and equality is invariant under
exchange, hence the full contact is reversible even off the prepared domain.
From baseline r, k!=1+r sends exactly 1+r units around the bus and leaves
stock x at its source. All other r taps pass it through; only the original
mismatch redirects it to D, restoring k and r. A matched input bypasses the
bus unnoticed. Cascade r=0 then r=1, merging completions by singleton vs
larger restored load. The shared reporter's cold exchange sends one physical
unit round ONE fixed four-edge meter loop for either bus. Its two local port
maps distinguish the buses by the SAME symmetric equality at departure and
return. Counting one designated meter edge now costs no source address, time
weight, remote freeze/broadcast, or preset schedule.

Each observed rail supplies TWO reciprocal rings through all its taps, one
extra stationary unit per baseline-one tap, and a distinct meter link at
the common observer location. There is not a single unlabelled edge that
magically identifies the rail. Only one occupied bunch moves globally in
the normal instrument. The main graph resumes through its original incidence
after return; propagation can be arbitrarily slow but must be finite in each
direction. Delays are diagnostics, never routing input. The ring direction,
ports, cold meter, preparation, passive (non-absorbing) observation and
single-request restriction are resources, not derived material dynamics.
The conserved material now includes the bus baseline units; only the bare
petal had just two units. Reverse traversal of an occupied logical bond uses
the SAME installed interposer in reverse. A clean served hop on an n-tap rail
costs n+8 edge traversals for k>1, n+9 for k=1 (one extra cascade edge).
Source port numbers are local to the vertex; no hidden address travels with k.
"""

from collections import Counter
from itertools import pairwise, product

from scripts.probe_bipartite_triangle_origin import need
from scripts.probe_indistinguishable_mobile_load import Mesh, Walk, exchange


def paired(names, pairs):
    table = {p: p for p in names}
    for a, b in pairs:
        table[a], table[b] = b, a
    return table


class Half:
    def __init__(self, at, port):
        self.at, self.port = at, port
        self.peer = None
        self.cost, self.meter = 0, None


class Node:
    def __init__(self, equal, other, native=False, stock=0):
        self.equal, self.other = equal, other
        self.native, self.stock = native, stock
        self.ports = {p: Half(self, p) for p in equal}

    def rule(self, port, k, s):
        equality = (k - 1 == s) if self.native else (k == 1)
        outgoing = (self.equal if equality else self.other)[port]
        k, s = exchange(k, s) if self.native else (k, s)
        return outgoing, k, s

    def scatter(self, port, k):
        out, k, self.stock = self.rule(port, k, self.stock)
        return self.ports[out], k


TAP = ("A", "F", "D", "-", "+")


def tap(r):
    return Node(
        paired(TAP, (("A", "F"), ("-", "+"))),
        paired(TAP, (("A", "+"), ("-", "D"))),
        True,
        r,
    )


def relay():
    table = {"L": "R", "R": "L"}
    return Node(table, table)


class Device:
    def __init__(self, sizes, weighted=False):
        self.base = Mesh(sizes, 1)
        self.main, self.taps, self.meters, self.baseline = {}, {}, {}, {}
        self.nodes, self.outlet = [], {}
        self.links, self.weighted = 0, weighted
        for old in {p.at for p in self.base.index.values()}:
            # Only installation and cross-model checks use the original
            # graph's named incidences; a running vertex sees local sockets.
            socket = {p: j for j, p in enumerate(old.ports)}
            through = {socket[p]: socket[q] for p, q in old.through.items()}
            switched = {socket[p]: socket[q] for p, q in old.marked.items()} or through
            main = Node(through, switched, old.stores)
            self.main[old] = self.install(main)
            self.outlet.update({p: main.ports[j] for p, j in socket.items()})
        self.mainset = set(self.main.values())
        for i in self.base.order:
            self.rail(i, sizes[i])
        need(
            all(p.peer is not None for v in self.nodes for p in v.ports.values()),
            "unconnected installed port",
        )

    def install(self, v):
        self.nodes.append(v)
        return v

    def wire(self, a, p, b, q, meter=None):
        x, y = a.ports[p], b.ports[q]
        need(x.peer is None and y.peer is None and x is not y, "port already occupied")
        self.links += 1
        x.peer, y.peer = y, x
        x.cost = y.cost = 1 + self.links % 7 if self.weighted else 1
        x.meter = y.meter = meter

    def rail(self, i, count):
        names = ("I0", "O0", "I1", "O1", "P", "Q")
        meter = self.install(
            Node(
                paired(names, (("I0", "P"), ("Q", "O0"))),
                paired(names, (("I1", "P"), ("Q", "O1"))),
                True,
            )
        )
        self.meters[i] = meter
        self.baseline[meter] = 0
        loop = [self.install(relay()) for _ in range(3)]
        self.wire(meter, "P", loop[0], "L")
        self.wire(loop[0], "R", loop[1], "L", meter=i)
        self.wire(loop[1], "R", loop[2], "L")
        self.wire(loop[-1], "R", meter, "Q")
        for j in range(count):
            p, q = (self.base.index[i, j, d] for d in (1, -1))
            a, b = self.main[p.at], self.main[q.at]
            t, u = self.install(tap(0)), self.install(tap(1))
            self.taps[i, j, 0], self.taps[i, j, 1] = t, u
            self.baseline[t], self.baseline[u] = 0, 1
            names = ("D0", "D1", "O")
            merge = self.install(
                Node(paired(names, (("D1", "O"),)), paired(names, (("D0", "O"),)))
            )
            self.wire(a, self.outlet[p].port, t, "A")
            self.wire(t, "F", u, "A")
            self.wire(t, "D", merge, "D0")
            self.wire(u, "D", merge, "D1")
            self.wire(merge, "O", b, self.outlet[q].port)
            cap = self.install(Node({"x": "x"}, {"x": "x"}))
            self.wire(u, "F", cap, "x")  # unreachable in clean serial operation
        for r in (0, 1):
            row = [self.taps[i, j, r] for j in range(count)]
            self.wire(meter, f"O{r}", row[0], "-")
            for left, right in pairwise(row):
                self.wire(left, "+", right, "-")
            self.wire(row[-1], "+", meter, f"I{r}")

    def launch(self, old, k):
        return Pulse(self.outlet[old], k)

    def clean(self):
        return all(v.stock == r for v, r in self.baseline.items())

    def snapshot(self):
        return tuple(n.stock for n in self.nodes)


class Pulse:
    def __init__(self, port, k):
        self.out, self.k = port, k

    def step(self, book):
        old, k = self.out, self.k
        book["hops"] += 1
        book["time"] += old.cost
        if old.meter is not None:
            book["meter", old.meter] += k
        arrival = old.peer
        self.out, self.k = arrival.at.scatter(arrival.port, k)
        return arrival.at, k

    def undo(self):
        # Every local contact is an involution, not just the matched case.
        arrival, self.k = self.out.at.scatter(self.out.port, self.k)
        self.out = arrival.peer


def to_main(bus, pulse, book):
    for _ in range(10000):
        v, k = pulse.step(book)
        if v in bus.mainset:
            return k
    raise AssertionError("no return within fixture budget")


def local_audit(bus):
    for v in bus.nodes:
        for p, k, s in product(v.ports, range(1, 9), range(9)):
            q, a, b = v.rule(p, k, s)
            need(
                a + b == k + s and v.rule(q, a, b) == (p, k, s),
                "off-promise local inverse",
            )
    for r in range(4):
        v = tap(r)
        need(
            v.rule("A", r + 1, r) == ("F", r + 1, r),
            "single tap not blind at matching load",
        )


def serial(bus, old, k):
    before = bus.snapshot()
    pulse = bus.launch(old, k)
    first = pulse.out
    book = Counter()
    arrived = to_main(bus, pulse, book)
    i = old.name[0]
    need(
        arrived == k and bus.clean() and book["meter", i] == 1,
        "load or bus not restored",
    )
    need(pulse.out.at is bus.main[old.peer.at], "completion reached a different bond")
    for _ in range(book["hops"]):
        pulse.undo()
    need(
        pulse.out is first and pulse.k == k and bus.snapshot() == before,
        "full reverse failed",
    )
    return book


def integrated(weighted):
    ns = (2, 1, 3)
    bus = Device(ns, weighted)
    bare = Walk(bus.base.ends[0, 1], 2)
    pulse = bus.launch(bare.port, 2)
    start = bare.state()
    delivered, book = Counter(), Counter()
    while True:
        expected, load = bare.tick()
        arrived = to_main(bus, pulse, book)
        delivered[expected] += 1
        need(
            arrived == load
            and pulse.k == bare.k
            and pulse.out is bus.outlet[bare.port]
            and bus.clean(),
            "interposed route diverged",
        )
        need(
            all(bus.main[v].stock == bare.parked.get(v, 0) for v in bus.base.cells),
            "altered source cell",
        )
        if bare.state() == start:
            break
        need(delivered.total() < 100, "bare orbit did not close")
    need(
        delivered == {0: 4, 1: 1, 2: 9}
        and all(book["meter", i] == n for i, n in delivered.items()),
        "not an observed square profile",
    )
    need(
        book["hops"] == 156 and sum(bus.baseline.values()) == sum(ns),
        "unaccounted travel or baseline inventory",
    )
    return book["hops"], book["time"]


def overlap():
    bus = Device((4,))
    starts = [bus.base.index[0, j, 1] for j in (0, 2)]
    ref = bus.snapshot()
    waves = [bus.launch(starts[0], 2), bus.launch(starts[1], 3)]
    initial = [(p.out, p.k) for p in waves]
    trace, book = [], Counter()
    for p in waves:  # both injections before either reporter reaches the other tap
        p.step(book)
        trace.append(p)
    need(
        [p.k for p in waves] == [1, 1]
        and [bus.taps[0, j, 0].stock for j in (0, 2)] == [1, 2],
        "two defects not installed",
    )
    arrivals = {}
    for p in waves:
        for _ in range(100):
            at, k = p.step(book)
            trace.append(p)
            if at in bus.mainset:
                arrivals[at] = k
                break
        else:
            raise AssertionError("overlap failed to terminate")
    expected = {bus.main[a.peer.at]: k for a, k in zip(starts, (2, 3), strict=True)}
    need(
        arrivals == expected and bus.clean() and book["meter", 0] == 1,
        "two jobs did not complete with just one real meter crossing",
    )
    # Histories are used only to audit the inverse, never as routing labels.
    for p in reversed(trace):
        p.undo()
    need(
        [(p.out, p.k) for p in waves] == initial and bus.snapshot() == ref,
        "overlap inverse",
    )


def controls(bus):
    old = bus.base.index[0, 0, 1]
    # Dirty meter: not on the clean serial contract, but still reversible.
    meter = bus.meters[0]
    meter.stock = 1
    need(meter.rule("I0", 1, 1) == ("I0", 2, 0), "dirty meter silently idealized")
    wave = bus.launch(old, 3)
    initial, start = bus.snapshot(), wave.out
    history = Counter()
    returned = to_main(bus, wave, history)
    need(
        returned == 1 and history["hops"] == 5 and history["meter", 0] == 0,
        "an unprepared meter must not inherit the serial readout guarantee",
    )
    for _ in range(history["hops"]):
        wave.undo()
    need(
        bus.snapshot() == initial and wave.out is start and wave.k == 3,
        "dirty global inverse",
    )
    meter.stock = 0
    # If the singleton is absorbed instead of passively observed, it cannot
    # return to release the two units parked by the three-unit issue.
    wave = bus.launch(old, 3)
    for _ in range(50):
        if wave.out.meter is not None:
            break
        wave.step(history)
    need(
        wave.out.meter == 0 and wave.k == 1 and bus.taps[0, 0, 0].stock == 2,
        "no explicit incomplete state at destructive observation",
    )


def main():
    bus = Device((2, 1, 3))
    local_audit(bus)
    for old, k in product(bus.base.index.values(), range(1, 10)):
        serial(bus, old, k)
    fast, slow = integrated(False), integrated(True)
    need(
        fast == (156, 156) and slow[0] == 156 and slow[1] > fast[1],
        "heterogeneous delay countercontrol",
    )
    overlap()
    controls(bus)
    print(
        f"common observer counts 4/1/9; 156 traversals, elapsed costs {fast[1]} vs {slow[1]}"
    )
    print(
        "one measured unit on one physical meter edge per rail, both baseline buses restored"
    )
    print(
        "two simultaneous defects: two restored completions but ONE measured crossing; serial only"
    )


if __name__ == "__main__":
    main()
