"""Exclusive named ports on the neutral triangle; no spatial triangle assumed.

Write P_i for the exchange fixing i, C for a three-cycle and J=I+C+C².
Issue P_i (positive), C and C² (reversed) paths to register i: on net this
is T_i=I+P_i-J. A tenth rail collects one positive path from every input.
On neutral v its current is zero, and T_i v=v_i m_i for m_i=3e_i-1.
The raw integer columns, including this sum rail, have Gram 6I. The
existing alternating-path router can therefore carry all six descendants
of each original addressed same-rail ordered pair to unique terminals.

There are two separate arguments. If previous bright, whole-packet stock
rigidity applies (W proportional to Q=sum v_j²/2), *each entire register*
has W(T_i v) proportional to 3v_i². No per-rail additivity within a
register is needed for this ratio. It takes matched registers, additivity
of distinct terminal bins, and frequencies proportional to stock to turn
this into a probability. Separately, the addressed implementation supplies
the signed cloud, coherent path cancellation, all same-rail ordered pairs
with replacement, a uniform original ticket and an independent uniform
six-way seed. It neither selects a physical initial event nor derives this
sampling rule. Reading the input ticket's rail already gives the same bare
histogram; the routed addresses and outgoing signed currents are additional
tests. This is an explicit instrument, not uniquely forced wiring.

Comparison class: only the three old normalized two-outcome projective
instruments, on ONE unknown neutral ray. The first instrument projects
onto its known median or edge; on each nonzero branch every later normalized
experiment is independent of the original ray. Thus arbitrary later
settings, classical randomness and labels reduce to a stochastic labelling
of the first dial/outcome. No side information, copies, reading the branch
magnitude/original address, or coherent control before that measurement.
The target effects are (2/3) times the median projectors: m_i.v=3v_i,
||m_i||²=6. Positivity and the target zero on edge i alone exclude every
first edge outcome from label i, and exclude other dials' median outcomes.
For exact heralded proportions with uniform efficiency eta, on median i the
weight of first choosing dial i and accepting its + must be 2eta/3.
Summing gives eta<=1/2. The six-state dual below also treats total labelling
with errors. No all-instrument no-go or physical absorption law is asserted.

Run: python3 -B -O -m scripts.probe_exclusive_triangle_detector
"""

from collections import Counter
from fractions import Fraction as F
from itertools import product

from scripts.probe_triangle_exchange_source import (
    D, edge, initialize, median, need, norm, pairs, route_block, signed_split,
    transposition,
)
from scripts.probe_triangle_stock_rigidity import inputs, quadratic


def build_gate():
    """Raw children are routes, not fractions or assignments to named tickets."""
    cols = []
    for src in D:
        paths = [(9, 1)]  # One scalar drain, not a copy of the three rails.
        for dial in D:
            for dest, sign in ((transposition(dial)[src], 1),
                               ((src+1) % 3, -1), ((src+2) % 3, -1)):
                paths.append((3*dial + dest, sign))
        # Calibrate a single parent: subtract opposite coincident paths BEFORE
        # the integer-column router creates children of different parents.
        col = [0] * 10
        for rail, sign in paths:
            col[rail] += sign
        need(len(paths) == 10 and sum(map(abs, col)) == 6, "path calibration")
        cols.append(col)
    return tuple(zip(*cols, strict=True))


def gram(rows):
    return tuple(tuple(sum(r[a]*r[b] for r in rows) for b in D) for a in D)


def calibrate(gate):
    def target(diag, every):
        return tuple(tuple(diag*(a == b)+every for b in D) for a in D)
    naive = tuple(r for i in D for r in signed_split(transposition(i))[:3])
    need(gram(naive) == target(6, 2), "stacking positive arms is not tight off-plane")
    need(gram(gate[:-1]) == target(6, -1), "missing uniform mode correction")
    need(gram(gate) == target(6, 0), "ambient gain-six calibration")
    for i, row in enumerate(gate[:-1]):
        k, d = divmod(i, 3)
        need(row == tuple(int(d == j)+int(d == transposition(k)[j])-1
                          for j in D), "raw-path column identity")


def route(v, gate, reverse):
    source = initialize(v)
    cloud, paths, gain, longest = route_block(source.cloud, gate, reverse)
    need(gain == 6, "wrong seed multiplicity")
    posted, labels = set(), {}
    for name, address in source.tickets.items():
        for seed in range(gain):
            dest = paths[address, seed]
            a, b = dest
            need(cloud[a][0] == cloud[b][0] and dest not in posted, "nonexclusive terminal")
            posted.add(dest)
            labels[name, seed] = cloud[a][0] // 3  # drain -> 3
    need(posted == pairs(cloud) and len(labels) == gain*len(source.tickets),
         "lost or invented descendant")
    current = tuple(sum(s for j, s in cloud if j == r) for r in range(10))
    events = Counter(labels.values())
    return current, tuple(events[i] for i in range(4)), labels, longest


def routed_controls(gate):
    changed, crossed, biased, longest = 0, 0, 0, 0
    samples = [v for v in inputs(3) if any(v)] + [(4,-3,-1)]
    for v in samples:
        x, count, labels, n = route(v, gate, False)
        y, other, alt, m = route(v, gate, True)
        need(x == y and count == other, "matching changes observable")
        need(x == tuple(v[i]*z for i in D for z in median(i)) + (0,),
             "routed register currents")
        whole = tuple(quadratic(x[3*i:3*i+3]) for i in D)
        need(whole == tuple(3*z*z for z in v), "whole-register stock ratio")
        need(count == tuple(2*w for w in whole) + (0,), "sixfold ticket tally")
        source = initialize(v)
        for name, addr in source.tickets.items():
            issued = tuple(labels[name, seed] for seed in range(6))
            crossed += sum(i != source.cloud[addr[0]][0] for i in issued)
            biased += int(any(issued.count(i)*norm(v) != 6*v[i]**2 for i in D))
        changed += sum(labels[key] != alt[key] for key in labels)
        longest = max(longest, n, m)
    need(changed and crossed and biased, "individual-address countercontrols")
    # The input (1,1,1) is intentionally outside the operational neutral plane.
    # Ignoring the drain would count nine of eighteen events, then normalize.
    x, count, _, _ = route((1,1,1), gate, False)
    need(x == (-1,)*9+(3,) and count == (3,3,3,9), "bright uniform drain")
    need(route((0,0,0), gate, False)[1] == (0,0,0,0), "zero is no event")
    return len(samples), changed, crossed, biased, longest


def binary_plus(v, dial):
    source = initialize(v)
    gate = signed_split(transposition(dial))
    cloud, paths, gain, _ = route_block(source.cloud, gate)
    yes = sum(cloud[dest[0]][0] < 3 for dest in paths.values())
    need(gain == 4 and len(paths) == 4*norm(v), "old instrument")
    return F(yes, len(paths))


def simulator_controls():
    # Only these physically wired six-state tables enter the exact dual.
    states = tuple(median(i) for i in D) + tuple(edge(i) for i in D)
    plus = {(v,j): binary_plus(v,j) for v in states for j in D}
    ideal = {(v,i): F(v[i]**2, norm(v)) for v in states for i in D}
    def score(tab):
        return sum(tab[median(i),i] - tab[edge(i),i] for i in D)

    need(score(ideal) == 2, "ideal dual score")
    best, vertices, herald_vertices = 0, 0, 0
    exact, approximate = Counter(), Counter()
    for j in D:
        # Stochastic labels are convex mixtures of these deterministic pairs.
        for a, b in product(range(4), repeat=2):
            # 3 means no label (heralded rejection).
            t = {(v,i): (a == i)*plus[v,j] + (b == i)*(1-plus[v,j])
                 for v in states for i in D}
            zeros = all(t[edge(i),i] == 0 for i in D)
            need(zeros == (b == 3 and a in (j,3)), "positive zero-cell witness")
            if zeros:
                herald_vertices += 1
            if a == j and b == 3:
                for key in t:
                    exact[key] += t[key]/3  # uniform dial; keep only +
            if 3 not in (a,b):
                vertices += 1
                best = max(best, score(t))
                if a == j and b != j:
                    for key in t:
                        approximate[key] += t[key]/6  # - chooses one of the other two
    need(vertices == 27 and herald_vertices == 6 and best == F(3,2),
         "extreme strategy certificate")
    need(all(exact[key] == p/2 for key,p in ideal.items()), "exact half throughput")
    visibility = best/score(ideal)
    lower = (score(ideal)-best)/6  # discrepancy is a signed sum of six cells
    need(visibility == F(3,4) and score(approximate) == best and
         all(approximate[k] == visibility*p+(1-visibility)/3 for k,p in ideal.items())
         and max(abs(approximate[k]-p) for k,p in ideal.items()) == lower == F(1,12),
         "symmetric visibility and sharp cell error")
    # Same attainments on every neutral input: plus_j=(3/2)*ideal_j by
    # the matrix identity on the neutral plane, and sum_j plus_j=3/2.
    # Substitution in the two displayed classical labellings is affine.
    for v in ((2,1,-3), (4,-3,-1)):
        u = [binary_plus(v,j) for j in D]
        for i in D:
            p = F(v[i]**2,norm(v))
            need(u[i]/3 == p/2 and
                 u[i]/3+sum(1-u[j] for j in D if j != i)/6 == (3*p)/4+F(1,12),
                 "off-ray strategy wiring")
    return vertices, best, visibility, lower


def main():
    gate = build_gate()
    calibrate(gate)
    n, changed, crossed, biased, longest = routed_controls(gate)
    vertices, best, visibility, error = simulator_controls()
    print(f"Raw paths -> Gram 6I; {n} nonzero neutral currents, both matchings; "
          f"6 seeds per addressed pair, no rejection, one named terminal per seed.")
    print(f"Matching changed {changed} ticket labels; {crossed} labels differ from input rail; "
          f"{biased} fixed input addresses miss the target under six seeds alone; longest walk {longest}.")
    print("(2,1,-3): ticket bins (24,6,54)/84; uniform (1,1,1) control: (3,3,3;9 drain)/18.")
    print(f"Single unknown ray, normalized native binary instruments: exact heralding <=1/2, "
          f"attained. {vertices} total-label vertices; six-cell dual {best} vs 2, "
          f"sharp visibility {visibility}, sharp worst-cell error {error}.")
    print("Conditional whole-register W proportional to Q; matched additive registers and uniform "
          "tickets/seeds supplied. Physical one-event selection is open.")


if __name__ == "__main__":
    main()
