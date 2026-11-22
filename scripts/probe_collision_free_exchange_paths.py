"""Exchange without a double occupation: minimal nuisance-matched routes on a Y.

Supply two indistinguishable hard-core occupations, one move along one
spatial edge per equal-duration tick, and no collisions. Unordered positions
are the observed states. Temporarily ordering the two INITIAL positions is
a mathematical lift: which position moved is uniquely determined by the two
consecutive observed sets. The lift has no phase, particle identity detector
or occupancy-dependent sign rule. On a path the relative order never changes;
on the bare three-arm star the six unordered configurations form a ring and
one lap exchanges the initial positions. The ordered ring has twelve states.

A pair of ten-tick loops has equal counts of visited UNORDERED configurations
and of directed SPATIAL bonds. It cancels arbitrary common static scalar
factors per occupied pair per tick and per oriented spatial bond in the
relative amplitude (provided it is nonzero). Count departures; the two loops
also have the same arrival counts and final state. Time-dependent fields,
route/controller delays, label-dependent couplings, which-route records and
transition phases depending on the spectator need not cancel.

There is a finite lower bound: an odd-winding exchange visits all six sites
of the configuration ring. So must the matched nonexchange loop. Below
twelve ticks an even-winding loop must have winding zero; the closed lift
to the integer line must span >= 5 steps and return, taking >= 10 ticks.
The directed spatial edge constraint still admits a length-ten witness.
This minimum is for these observables, hard-core moves and this graph.

Coherent comparison SUPPLIES a route splitter, two programmed sequences of
local moves with no lasting route record, a signed even/odd preparation of
the ordered sheets, matched timing, a route recombiner and squared-norm
detection. Neither a physical sheet reference nor any of those controls
comes from two unlabeled positions alone. Both character sectors can be tested in the
SAME abstract cover. In particular the double cover gives a permutation,
not a law of statistics: on the unordered ring an arbitrary U(1) holonomy
per winding is possible. A reciprocal minus sign on just ONE configuration
edge imitates the odd sheet on EVERY closed route. It is a countercontrol,
not part of the unsigned lift. No experimental result or particle verdict.
Run: python3 -B -m scripts.probe_collision_free_exchange_paths (also with -O).
"""

from collections import Counter
from fractions import Fraction as F
from itertools import combinations, pairwise, product

from scripts import gaussian_dyadic_words as w

Y = ((0,1), (0,2), (0,3))
PATH = ((0,1), (1,2), (2,3))
# This chooses a base point and a direction for indexing, not a phase.
RING = ((1,2), (0,2), (2,3), (0,3), (1,3), (0,1))
EXCHANGE = (0,1,2,3,2,3,4,5,0,1,0)
REFERENCE = (0,1,2,3,4,3,2,1,0,5,0)


def need(test, detail):
    if not test:
        raise ArithmeticError(detail)


def configuration_graph(bonds):
    sites = sorted({p for edge in bonds for p in edge})
    neighbors = {c: {} for c in combinations(sites, 2)}
    for c, exits in neighbors.items():
        for a,b in bonds:
            for old,new in ((a,b),(b,a)):
                if old in c and new not in c:
                    d = tuple(sorted((set(c) - {old}) | {new}))
                    exits[d] = (old,new)
    return neighbors


def carry(order, step):
    old,new = step
    need(old in order and new not in order, "ordered lift violated hard core")
    return tuple(new if x == old else x for x in order)


def transport(order, moves):
    for step in moves:
        order = carry(order, step)
    return order


def check_graphs():
    line = configuration_graph(PATH)
    # Checking order on every allowed elementary move proves it for every
    # concatenation; disjoint-particle timing squares on a path can still exist.
    for c, adj in line.items():
        for d, step in adj.items():
            need(carry(c,step) == d and carry(c[::-1],step) == d[::-1], "path order changed")
    star = configuration_graph(Y)
    n = len(RING)
    need(set(star) == set(RING) and all(set(star[c]) ==
         {RING[(j-1)%n], RING[(j+1)%n]} for j,c in enumerate(RING)), "Y is not C6")
    start = RING[0]
    ordered = [start]
    for j in range(2*n):
        ordered.append(carry(ordered[-1], star[RING[j%n]][RING[(j+1)%n]]))
    need(ordered[n] == start[::-1] and ordered[-1] == start and
         len(set(ordered[:-1])) == 12, "ordered lift is not a full C12")
    return star


def trace(indices, graph):
    positions = tuple(RING[j] for j in indices)
    moves = tuple(graph[a][b] for a,b in pairwise(positions))
    return moves, transport(positions[0], moves)


def key_for(indices, moves):
    # Arrival and departure histograms coincide for a closed loop. Directed
    # physical edge counts distinguish the two directions separately.
    visits, bonds = Counter(indices[:-1]), Counter(moves)
    return tuple(visits[j] for j in range(6)), tuple(
        bonds[edge] for a,b in Y for edge in ((a,b),(b,a)))


def exhaustive_minimum(graph):
    # All starting configurations, both next neighbors, every length <=10.
    # A hash collision would be harmless: Python also compares exact tuples.
    hits = set()
    for n in range(11):
        for start in range(6):
            seen = set()
            for steps in product((-1,1), repeat=n):
                if sum(steps) % 6:
                    continue
                walk = [start]
                for h in steps:
                    walk.append((walk[-1]+h)%6)
                moves, final = trace(walk,graph)
                flip = final == RING[start][::-1]
                key = key_for(walk,moves)
                if (not flip,key) in seen:
                    hits.add(n)
                seen.add((flip,key))
    need(hits == {10}, "shortest matched exchange/reference pair changed")


def fake_on_edge(indices, cut):
    crossed = sum({a,b} == {cut,(cut+1)%6} for a,b in pairwise(indices))
    return (-1)**crossed


def signs_and_gauges(graph):
    # An antisymmetric section can use either ordering at each vertex as
    # its local basis. Flipping that choice changes adjacent edge signs but
    # telescopes on loops. All 2^6 choices, including a moving seam.
    for flags in product((0,1), repeat=6):
        frame = tuple(c[::-1] if f else c for c,f in zip(RING,flags))
        def lifted_sign(route, frame=frame):
            s = 1
            for j,k in pairwise(route):
                arrived = carry(frame[j],graph[RING[j]][RING[k]])
                s *= 1 if arrived == frame[k] else -1
            return s
        need(lifted_sign(EXCHANGE) == -1 and lifted_sign(REFERENCE) == 1,
             "change of local choice of order changed the holonomy")
    # For a closed walk, algebraic signed crossing number of any cut equals
    # winding. Its parity equals total (unsigned) crossings of that cut.
    # Thus a spectator-specific edge phase can copy the entire character,
    # not just the one pair. Test both senses and multiple windings/backtracks.
    for winding in range(-3,4):
        way = 1 if winding >= 0 else -1
        rr = REFERENCE + tuple((way*j)%6 for j in range(1,6*abs(winding)+1))
        _moves, end = trace(rr,graph)
        exact = 1 if end == RING[0] else -1
        need(all(fake_on_edge(rr,cut) == exact == (-1 if winding%2 else 1)
                 for cut in range(6)), "configuration-edge impostor failed")
    need(all(fake_on_edge(EXCHANGE,k) == -1 and fake_on_edge(REFERENCE,k) == 1
             for k in range(6)), "matched paths should not cancel configuration-edge phases")


def interferometer(exchange, reference):
    start, rev = RING[0], RING[0][::-1]
    # The arm controls specify only spatial bonds. For a selected trajectory
    # each gate moves into an empty site, irrespective of source ordering.
    # A reversible extension toggles the bond when exactly one end is occupied
    # (otherwise leaves positions still); no collision or tag-dependent swap.
    def pulse(order, bond):
        left,right = bond
        if (left in order) == (right in order):
            return order
        return carry(order, (left,right) if left in order else (right,left))

    for bond in Y:
        for order in product(range(4), repeat=2):
            if order[0] != order[1]:
                need(pulse(pulse(order,bond),bond) == order, "spatial pulse not reversible")

    def program(order, path):
        for old,new in path:
            # Only the unordered hardware bond is addressed in the pulse.
            moved = pulse(order, tuple(sorted((old,new))))
            need(moved == carry(order,(old,new)), "program left planned trajectory")
            order = moved
        return order

    for name, source, expected in (
        ("even", {start:w.ONE, rev:w.ONE}, (1,0)),
        ("odd", {start:w.ONE, rev:w.g(-1)}, (0,1)),
        ("ordered", {start:w.ONE}, (F(1,2),F(1,2))),
    ):
        routes = (reference,exchange)
        arms = [{program(label,path):z*coef for label,z in source.items()}
                for path,coef in zip(routes,(w.DIAG,w.CROSS))]
        p = [F(),F()]
        for label in (start,rev):
            x,y = (branch.get(label,w.ZERO) for branch in arms)
            for j,z in enumerate((w.DIAG.star()*x + w.CROSS.star()*y,
                                  w.CROSS.star()*x + w.DIAG.star()*y)):
                p[j] += z.norm2()
        norm = sum(z.norm2() for z in source.values())
        need(tuple(n/norm for n in p) == expected, f"{name}: routed readout")
        # A classical mixture of the two initial orderings has the same
        # half/half outputs as either ordering, not the pure odd dark port.


def main():
    graph = check_graphs()
    exhaustive_minimum(graph)
    exchange, sw = trace(EXCHANGE,graph)
    reference, ret = trace(REFERENCE,graph)
    k = key_for(EXCHANGE,exchange)
    need(RING[0] == ret == sw[::-1] and len(exchange) == len(reference) == 10
         and k == key_for(REFERENCE,reference) == ((2,2,2,2,1,1),)*2,
         "matched spatial moves/visits or lift changed")
    signs_and_gauges(graph)
    interferometer(exchange,reference)
    print("Path: order conserved. Bare Y: unordered C6, ordered C12; one lap swaps.")
    print(f"Y configurations: {RING}. Ten-tick exchange / identity: {EXCHANGE} / {REFERENCE}.")
    print(f"Departure counts {k[0]}; directed 01,10,02,20,03,30 counts {k[1]}."
          " No shorter matched pair. Bright-port probabilities: odd 0, even 1, definite order 1/2.")
    print("The unsigned lift fixes only the permutation. A configuration-edge phase"
          " copies the odd holonomy. Coherent apparatus and physical sector are supplied.")


if __name__ == "__main__":
    main()
