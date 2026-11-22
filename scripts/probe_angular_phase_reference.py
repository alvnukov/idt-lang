"""Can a measured angular role transport serve as a two-triangle reference?

Discriminator fixed in advance: first straight reunions in the supplied
translation/glide/screw quotients must act on the three opposite-square
pairs by identity/transposition/transposition. Their signed-frame determinants
must instead be +/−/+. A phase device wired to exactly one transported triple
should therefore repeat/swap/swap its K herald. Co-transport and decoupled
controls should repeat throughout; an independent relative reversal should
reverse these answers. No parity bit is an input to the ticket router.

The observer gets a starting station, stable reunion IDs, complete neighbor
discovery and reciprocal shell incidence. The graph transport below is a
prescription tested on those fixtures; no coordinates, axis names or seam
generators enter it. The association of phase rails with geometric roles
is additional wiring, not a consequence of the graph or a spin/space law.

Run: python3 -B -O -m scripts.probe_angular_phase_reference
"""

import sys
from collections import Counter
from functools import cache
from itertools import combinations, permutations, product
from pathlib import Path

if not __package__:
    sys.path.insert(0, str(Path(__file__).resolve().parents[1]))

from scripts import probe_relational_chart_holonomy as holonomy
from scripts import probe_triangle_cycle_phase_axis as phase

need = phase.need
ID = (0, 1, 2)
ALL = tuple(permutations(ID))


def only(options):
    (value,) = options
    return value


def parity(p):
    return (-1) ** sum(p[i] > p[j] for i, j in combinations(ID, 2))


class Shell:
    def __init__(self, tags, adjacent):
        # Order enumerates the anonymous inputs only. A square is an induced
        # connected degree-two graph on four vertices (four forces connected).
        self.links = {s: set() for s in tags}
        for s, t in combinations(tags, 2):
            if adjacent(s, t):
                self.links[s].add(t)
                self.links[t].add(s)
        self.faces = tuple(
            frozenset(q)
            for q in combinations(tags, 4)
            if all(len(self.links[s].intersection(q)) == 2 for s in q)
        )
        need(len(self.faces) == 6, "not six induced squares")
        self.opp = {f: only(g for g in self.faces if f.isdisjoint(g)) for f in self.faces}
        self.roles = tuple(dict.fromkeys(frozenset((f, self.opp[f])) for f in self.faces))
        need(len(self.roles) == 3, "not three opposite-square pairs")
        self.inc = {s: frozenset(f for f in self.faces if s in f) for s in tags}
        self.ray = {a: s for s, a in self.inc.items()}
        need(len(tags) == len(self.ray) == 12 and all(len(a) == 2 for a in self.ray),
             "square incidences do not label all rays uniquely")
        self.back = {s: self.ray[frozenset(self.opp[f] for f in a)]
                     for s, a in self.inc.items()}

    def verify_map(self, target, face_map):
        need(set(face_map) == set(self.faces) and set(face_map.values()) == set(target.faces),
             "not a square bijection")
        mapped = {s: target.ray[frozenset(face_map[f] for f in a)]
                  for s, a in self.inc.items()}
        need(all({mapped[v] for v in ns} == target.links[mapped[s]]
                 for s, ns in self.links.items()), "not an isomorphism of angular graphs")
        return mapped

    def chosen(self, role):
        return next(f for f in self.faces if f in role)

    def signed_return(self, faces):
        p, end_sign = [], 1
        for role in self.roles:
            f = self.chosen(role)
            target = frozenset(faces[g] for g in role)
            p.append(self.roles.index(target))
            end_sign *= 1 if faces[f] == self.chosen(target) else -1
        return tuple(p), parity(p) * end_sign

    def symmetries(self):
        # Exhausts possibilities: every graph automorphism maps induced
        # squares to induced squares, respects disjointness, and is determined
        # on rays by the incident face pair. Check that ALL choices work.
        summary = Counter()
        for p, flips in product(ALL, product((0, 1), repeat=3)):
            fm = {}
            for i, role in enumerate(self.roles):
                a, b = self.chosen(role), self.chosen(self.roles[p[i]])
                if flips[i]:
                    b = self.opp[b]
                fm[a], fm[self.opp[a]] = b, self.opp[b]
            self.verify_map(self, fm)
            perm, det = self.signed_return(fm)
            summary[perm, det] += 1
        need(summary == Counter({(p, d): 4 for p in ALL for d in (-1, 1)}),
             "bare-shell role or orientation bias")


def measure(root, neighbors, adjacent, gauge, budget=10):
    """Pure incidence reader. Reindex independently at each station."""
    @cache
    def shell(s):
        tags = sorted(neighbors(s), key=lambda t: holonomy.digest(f"{gauge}/{s}/{t}"))
        return Shell(tags, adjacent)

    @cache
    def step(x, y):
        a, b = shell(x), shell(y)
        shared = a.links.keys() & b.links.keys()
        need(len(shared) == 4, "edge must have four shared stations")
        ahead = b.back[x]
        pins = {y: ahead}
        for u in shared:
            # In the new shell, u is the old common landmark viewed from y.
            # Complete the angular triangle with the forward continuation;
            # no affine coordinates are used to identify its unique solution.
            pins[u] = only(b.links[u] & b.links[ahead])
        pins.update({a.back[k]: b.back[v] for k, v in pins.items()})
        need(len(pins) == len(set(pins.values())) == 10, "ambiguous edge pins")
        fm = {f: only(g for g in b.faces if all((k in f) == (v in g)
                                                for k, v in pins.items())) for f in a.faces}
        full = a.verify_map(b, fm)
        need(all(full[k] == v for k, v in pins.items()), "completion lost a pin")
        return fm

    start = shell(root)
    start.symmetries()
    identity = {f: f for f in start.faces}

    def along(path):
        fm = identity
        for x, y in zip(path, path[1:]):
            trans = step(x, y)
            fm = {f: trans[g] for f, g in fm.items()}
        return fm

    tri = 0
    for x, y in combinations(start.links, 2):
        if y in start.links[x]:
            need(along((root, x, y, root)) == identity, "local triangle twists the faces")
            tri += 1
    need(tri == 24, "root triangle count")

    paths = [(root, x) for x in start.links]
    for tick in range(1, budget + 1):
        closed = [p for p in paths if p[-1] == root]
        if closed:
            returns, physical_maps = [], {}
            for p in closed:
                fm = along(p)
                need(along(p + p[1:]) == identity, "double reunion twists the faces")
                returns.append(start.signed_return(fm))
                physical_maps[p] = fm
            return tick, returns, physical_maps
        paths = [(*p, shell(p[-1]).back[p[-2]]) for p in paths]
    raise ValueError("no observed straight reunion within supplied budget")


def common_clock():
    # The diagonal orbit is the same set of paths for either 3-cycle.
    # Build the upper three-path columns directly from the even subgroup of
    # the role permutations, independently of phase.cycle_paths' winding.
    even = [p for p in ALL if parity(p) == 1]
    cols = [
        [int((c, d) in {(p[a], p[b]) for p in even}) for c, d in product(ID, repeat=2)]
        for a, b in product(ID, repeat=2)
    ]
    gate = tuple(zip(*cols, strict=True))
    for u in (1, -1):
        need(gate == phase.cycle_paths(1, (u, u))[:9], "common-triad cycle sum")
    return gate


def ticket_reader():
    source = phase.independent(phase.edge(0), phase.edge(0))
    prep, counts = phase.extend(source, phase.K, 1)
    need(counts == Counter({(0, 0): 18, (0, 1): 18}), "changed herald population")

    @cache
    def read(left, right):
        # Actual wiring of BOTH labels on every occupied paired rail. Preserve
        # carrier identity, sign, earlier herald and every parent ticket.
        cloud = []
        for rail, sign in prep.cloud:
            h, ab = divmod(rail, 9)
            a, b = divmod(ab, 3)
            cloud.append((9 * h + 3 * left[a] + right[b], sign))
        wired = phase.Stock(tuple(cloud), prep.tickets)
        need(phase.pairs(wired.cloud) == set(wired.tickets.values()), "lost pair addresses")
        _, outcomes = phase.extend(wired, phase.K, 2)
        return tuple(outcomes[h, b] for h, b in product((0, 1), repeat=2))

    return read


REPEAT, SWAP = (162, 0, 0, 162), (0, 162, 162, 0)


def main():
    common_clock()
    read = ticket_reader()
    for p, q in product(ALL, repeat=2):
        measured = read(p, q)
        need(measured == (REPEAT if parity(p) == parity(q) else SWAP),
             "actual ticket readout disagrees with relative role parity")
    alignments = Counter(read(ID, p) for p in ALL)
    need(alignments == Counter({REPEAT: 3, SWAP: 3}), "alignment classes")
    one_axis = [p for p in ALL if p[0] == 0]
    need({read(ID, p) for p in one_axis} == {REPEAT, SWAP}, "one-axis ambiguity")
    reverse_one = only(p for p in one_axis if p != ID)
    print("Bare root shell: 6 induced squares, 3 disjoint opposite pairs; all 48 signed "
          "role permutations preserve adjacency. No preferred role or winding.")
    print("Common triad: both 3-cycles give the same simultaneous orbit sum. Separate "
          "triads: 6 alignments split 3:3 on K, even fixing one role leaves both results.")
    print("36 paired wirings: 18 tickets per herald × 9 descendants. Counts in herald/read "
          f"order (++,+−,−+,−−): repeat={REPEAT}, swap={SWAP}.")
    for seam, expected_det, expected_odd in (
        ("translation", 1, False), ("glide", -1, True), ("screw", 1, True)
    ):
        w = holonomy.Fixture(seam)
        witnesses = []
        baseline = None
        for gauge in ("ruler A", "private ruler B"):
            tick, returns, physical_maps = measure(w.origin, w.neighbors, w.adjacent, gauge)
            if baseline is None:
                baseline = physical_maps
            need(baseline == physical_maps, "station-local ordering changed the actual face maps")
            need(tick == 6 and len(returns) == 2, "straight reunion control")
            for p, det in returns:
                need(det == expected_det and sum(i != j for i, j in enumerate(p))
                     == 2 * expected_odd, "wrong signed or unsigned loop action")
                one, both, uncoupled = read(ID, p), read(p, p), read(ID, ID)
                need(one == (SWAP if expected_odd else REPEAT)
                     and both == uncoupled == REPEAT, "wiring discriminator")
                mismatched = tuple(reverse_one[j] for j in p)
                need(read(ID, mismatched) != one, "missed reference reversal")
            witnesses.append(returns[0][0])
        print(f"{seam}: both first reunions at 6; role images by gauge {witnesses}; "
              f"signed determinant {expected_det:+}; K one/both/uncoupled = "
              f"{'swap' if expected_odd else 'repeat'}/repeat/repeat; "
              "mismatched reference reverses the first result.")
    print("24 root triangle circuits and double returns restore all six faces. Angular "
          "role transport alone selects no wiring and predicts no physical phase.")


if __name__ == "__main__":
    main()
