"""An internal reversible contact distinguishes worlds that ordinary ranging cannot.

Fixture, not a primitive derivation: start with the infinite least abelian
four-relation diamond quotient D of probe_internal_signal_geometry. Attach a
finite 16-state factor at every site, taking the Cartesian graph product.
R is the 4x4 rook graph; S is the Shrikhande graph. Both products have ten
ports, the same large-scale rank three, and are NOT the original four-port
candidate. Even the finite-factor coordinates are hidden from the reader.

For either finite adjacency A, A^2=4I+2J and AJ=6J, checked entrywise below.
Hence all powers have the same diagonal in both worlds (reduce to I,A,J).
On D x F the walk counter is B tensor I + I tensor A, whose terms commute.
For portals (u,f),(v,f) at ANY common fiber index f, the length-t walk
count is sum_j binom(t,j) (B^(t-j))[u,v] (A^j)[f,f], independent of F.
Uniform independent port choices divide this by 10^t. Requiring hits at
specified times multiplies those interval kernels; inclusion-exclusion for
the missed hits then gives identical joint click records for any prescribed
moving portals in that slice. This does not cover arbitrary off-slice
beacons, controlled port words, interacting signals or active memory.

Intervention: a three-hop word proposes a path 0-1-2-3 (path slots, NOT
site IDs). Test its missing chords 02,03,13. To test a~b, XOR the storage
bits of a's neighbors into a reply at home, toggle b, scan again, restore b.
Only their difference survives, even on dirty memory. A read uses a local
lane/store SWAP, takes the lane home, rotates a two-port home register if
lane 1, returns and swaps back. Toggle similarly uses a lane crossing at
home. The output is three ordinary bits, not a remote clique predicate.
On a simple graph channel 111 implies four distinct mutually adjacent sites.

Supplied: a home, locally enumerable stable reciprocal ports, reversible
transport insensitive to the lane, selectable bypass/SWAP contacts at
stations, crossed lanes, and a bounded home program with three output bits
and storage for at most three return ports. The petal detector supplies a
SWAP and lane-controlled hub routing, NOT this installed network/controller.
Simulation records no site IDs in the reader or in its return stack. The
decoder knows its own selected program; the graph fixture retains the cursor
address to implement local contact. Exhaustively counting programs is a lab
protocol, not a law selecting preparations or deriving physical observers.
Run: python3 -B -O -m scripts.probe_reversible_range_alias
"""

from collections import Counter
from functools import cache
from itertools import pairwise, product
from math import comb
from random import Random


def need(ok, why):
    if not ok:
        raise ValueError(why)


ZERO = (0, 0, 0, 0)
HOME = (ZERO, (0, 0))
FIBER = tuple(product(range(4), repeat=2))
STEPS = {
    "R": ((1, 0), (2, 0), (3, 0), (0, 1), (0, 2), (0, 3)),
    "S": ((1, 0), (-1, 0), (0, 1), (0, -1), (1, 1), (-1, -1)),
}


@cache
def diamond(x):
    sign = 1 if sum(x) == 0 else -1
    return tuple(x[:k] + (x[k]+sign,) + x[k+1:] for k in range(4))


@cache
def fiber(kind, u):
    return tuple(((u[0]+a) % 4, (u[1]+b) % 4) for a, b in STEPS[kind])


@cache
def neighbors(kind, v):
    x, u = v
    return tuple((y, u) for y in diamond(x)) + tuple((x, w) for w in fiber(kind, u))


def expand(dist, jumps):
    new = Counter()
    for u, m in dist.items():
        for v in jumps(u):
            new[v] += m
    return new


def passive(kind):
    for u, v in product(FIBER, repeat=2):
        need(len(set(fiber(kind, u)) & set(fiber(kind, v))) == 4*(u == v)+2,
             "fiber adjacency square")
    start = (0, 0)
    f = Counter([start])
    diagonals = []
    for _ in range(9):
        diagonals.append(f[start])
        f = expand(f, lambda u: fiber(kind, u))
    # All walks here are counted, not just geodesics. Derive comparison
    # intervals from D alone; use a separate full-product signal propagation.
    x1 = diamond(diamond(ZERO)[0])[1]
    x2 = diamond(diamond(x1)[0])[2]
    sites = (ZERO, x1, x1, x2, x1)
    epochs = (0, 2, 4, 6, 8)
    intervals = {}
    for i, u in enumerate(sites):
        walks = [Counter([u])]
        for _ in range(epochs[-1]-epochs[i]):
            walks.append(expand(walks[-1], diamond))
        for j in range(i+1, len(sites)):
            k = epochs[j]-epochs[i]
            intervals[i, j] = sum(comb(k, h)*diagonals[h]*walks[k-h][sites[j]]
                                  for h in range(k+1))
    # 'moments[m]' counts paths with all indicated sightings, unrestricted
    # elsewhere; Möbius inversion removes paths with unwanted extra sightings.
    moments = []
    for mask in range(16):
        selected = [0, *(j for j in range(1, 5) if mask & (1 << (j-1)))]
        ways = 10**(8-epochs[selected[-1]])
        for i, j in pairwise(selected):
            ways *= intervals[i, j]
        moments.append(ways)
    predicted = moments[:]
    for bit in (1, 2, 4, 8):
        for mask in range(16):
            if not mask & bit:
                predicted[mask] -= predicted[mask | bit]

    histories = {0: Counter([HOME])}
    returns = [1]
    for t in range(1, 9):
        histories = {h: expand(dist, lambda u: neighbors(kind, u))
                     for h, dist in histories.items()}
        returns.append(sum(dist[HOME] for dist in histories.values()))
        if t in epochs:
            i = epochs.index(t)
            target = (sites[i], start)
            detected = {}
            for h, dist in histories.items():
                count = dist.pop(target, 0)
                if count:
                    detected[h | (1 << (i-1))] = Counter({target: count})
            histories.update(detected)
    actual = [sum(histories.get(h, {}).values()) for h in range(16)]
    need(actual == predicted and sum(actual) == 10**8 and min(actual) > 0,
         "conditioned moving-portal transcript or empty fixture")
    return returns, actual


def installed(kind, seed):
    """Anonymous finite port interface; no experiment reaches the boundary."""
    nodes = {HOME}
    shell = {HOME}
    for _ in range(4):
        shell = {w for v in shell for w in neighbors(kind, v)} - nodes
        nodes.update(shell)
    rng = Random(seed)
    order = sorted(nodes)
    rng.shuffle(order)
    names = {v: i for i, v in enumerate(order)}
    rows = []
    for v in order:
        row = [names[w] for w in neighbors(kind, v) if w in nodes]
        rng.shuffle(row)  # a separately numbered port interface at EACH site
        rows.append(row)
    ports = [[(w, rows[w].index(i)) for w in row] for i, row in enumerate(rows)]
    return ports, names[HOME]


class Device:
    """Local actions only. Site ID is private to the cursor/edge backend."""

    def __init__(self, ports, home, seed):
        self._ports, self._at, self._home = ports, home, home
        rg = Random(seed)
        self._cells = bytearray(rg.randrange(2) for _ in ports)
        self.lane = rg.randrange(2)
        self.reply = 0

    def hop(self, p):
        self._at, back = self._ports[self._at][p]
        return back

    def swap_visit(self, word):
        # The inverse port of each physical hop is carried on board. Popping
        # it while retracing recovers the corresponding fixed forward port.
        back = [self.hop(p) for p in word]
        self.lane, self._cells[self._at] = self._cells[self._at], self.lane
        for p in reversed(word):
            need(self.hop(back.pop()) == p, "nonreciprocal hop")
        need(self._at == self._home, "did not return to home")

    def chord(self, a, b, slot, intervene=True):
        for _ in range(2):
            for p in range(10):
                wire = a + (p,)
                self.swap_visit(wire)
                self.reply ^= self.lane << slot  # lane-conditioned hub rotation
                self.swap_visit(wire)
            self.swap_visit(b)
            if intervene:
                self.lane ^= 1  # fixed lane crossing, at home
            self.swap_visit(b)

    def query(self, word, intervene=True):
        for slot, (a, b) in enumerate(((0, 2), (0, 3), (1, 3))):
            self.chord(word[:a], word[:b], slot, intervene)

    def hidden_state(self):
        """Audit only; the reader never gets this payload."""
        return self._at, self.lane, bytes(self._cells)


def local_components(kind):
    link = set(neighbors(kind, HOME))
    todo = set(link)
    sizes = []
    while todo:
        comp = {todo.pop()}
        frontier = comp.copy()
        while frontier:
            frontier = {w for v in frontier for w in neighbors(kind, v)} & todo
            comp.update(frontier)
            todo.difference_update(frontier)
        sizes.append(len(comp))
    degrees = [len(link & set(neighbors(kind, v))) for v in link]
    need(sorted(degrees) == [0]*4 + [2]*6, "unexpected root link")
    return sorted(sizes)


def active(kind, seed):
    ports, home = installed(kind, seed)
    dev = Device(ports, home, seed+1)
    initial = dev.hidden_state()
    bins = [0]*8
    for i, word in enumerate(product(range(10), repeat=3)):
        # The following is an independent CHECKER, not an operation of Device.
        trail = [home]
        for p in word:
            trail.append(ports[trail[-1]][p][0])
        want = sum((1 << k) for k, (a,b) in enumerate(((0,2),(0,3),(1,3)))
                   if any(w == trail[b] for w, _ in ports[trail[a]]))
        baseline = i % 8
        dev.reply = baseline  # checker tests all reply patterns
        dev.query(word)
        got = dev.reply ^ baseline
        need(got == want and dev.hidden_state() == initial, "dirty contact query")
        bins[got] += 1
        dev.query(word)
        need(dev.reply == baseline and dev.hidden_state() == initial, "not an involution")
        dev.query(word, intervene=False)
        need(dev.reply == baseline and dev.hidden_state() == initial, "sham changed state")
    return bins


def main():
    records = [passive(kind) for kind in ("R", "S")]
    need(records[0] == records[1], "passive twin mismatch")
    returns, histories = records[0]
    need(returns == [1,0,10,12,268,960,11512,69552,672412], "return control")
    print("Shared ordinary return counts at ticks 0..8:", returns)
    print("Four moving-portal observations: identical counts in all 16 click/miss channels;",
          "all-click walks:", histories[-1], "of", sum(histories))
    for kind, sizes, expected in (
        ("R", [1,1,1,1,3,3], [552,84,232,12,84,12,12,12]),
        ("S", [1,1,1,1,6], [564,72,220,24,72,24,24,0]),
    ):
        need(local_components(kind) == sizes, "neighbor graph components")
        for seed in ((11,29) if kind == "R" else (31,47)):
            need(active(kind, seed) == expected, "three-chord channels or relabeling")
        print(f"{kind}: local components {sizes}; dirty, restored three-bit channels {expected};"
              f" fully linked paths {expected[-1]}/1000; sham always zero difference.")
    print("Same supplied rank-three base, different local connectivity. Controlled routing and"
          " reversible memory access are inputs; neither dimension nor physical motion is derived.")


if __name__ == "__main__":
    main()
