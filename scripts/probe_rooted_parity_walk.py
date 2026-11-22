"""Signed path contrasts from an anonymous graph, not an installed charge table.

Given only adjacency, an absorbing start/vacuum r and a unit pulse at t,
count paths without touching r. Each tick either waits (one choice, sign
unchanged) or takes one incident edge (one choice per port, sign reversed).
No occupation coordinates, charge labels, additivity, complex amplitudes or
particle dictionary are used by the signal rule. This is *path counting*,
not a derivation of a particle's dynamics or one detector outcome.

Let A be adjacency on the 15 remaining vertices, with no rerouting of moves
into the absorber. The signed path recurrence is I-A. In the original
degree-five graph A0 has eigenvalues 5,1,-3 with multiplicities 1,10,5
(A0²=3I-2A0+2J). After deletion, interlacing retains respectively at
least nine 1s and four -3s. The two shell-constant eigenvalues come from
the quotient [[0,4],[2,3]], the roots of z²-3z-8. These exhaust the
15 dimensions. The most amplified eigenvalue of I-A is 4; the others
are 0 and (-1±sqrt(41))/2, strictly smaller in magnitude. Its multiplicity
is four, not one: the point at which the pulse is injected matters.

The polynomial 40P=-A³+4A²+5A-8I projects, up to the common scale, onto
that -3 eigenspace. Its coefficients are computed from the spectrum of this
graph. They are a finite analysis filter, not a proposed local law of nature.
We check P against its defining identities and an independent literal-path
counter before comparing the resulting field to the separate additive model.
All starts are counted in the optional positive sampler, including absorption
and misses. Signed contrast of two counts is not a probability or a charge
quantization measurement. Rounding to named integer units is a calibration.

Run: python3 -B -m scripts.probe_rooted_parity_walk
"""

from collections import Counter
from fractions import Fraction as F
from itertools import product
from math import gcd

from scripts.probe_anonymous_folded_carrier import forced_completion


def need(ok, why):
    if not ok:
        raise ArithmeticError(why)


def step(graph, root, state):
    return tuple(0 if u == root else sum(state[v] for v in nbs)
                 for u, nbs in enumerate(graph))


def basis(n, t):
    return tuple(int(v == t) for v in range(n))


def poly40(graph, root, raw):
    a = step(graph, root, raw)
    b = step(graph, root, a)
    c = step(graph, root, b)
    return tuple(-c[i]+4*b[i]+5*a[i]-8*raw[i] for i in range(len(graph)))


def paths(graph, root, point, n):
    """Literal event counts by independent depth-first path expansion; no matrix."""
    counts = Counter()

    def visit(v, remaining):
        if v == root:
            # Count all choices which would have remained after a first hit.
            counts[None] += 5**remaining
        elif not remaining:
            counts[v] += 1
        else:
            for w in graph[v]:
                visit(w, remaining-1)

    visit(point, n)
    need(sum(counts.values()) == 5**n, "lost an unconditional basic attempt")
    return counts


def primitive(vec):
    unit = gcd(*map(abs, vec))
    need(unit > 0, "zero field")
    return tuple(v//unit for v in vec)


def additive_reference(graph, root, point):
    """Comparison only: reconstruct coordinates AFTER generating walk outputs."""
    from scripts.probe_marked_carrier_charge import double_cover, port_block

    g = dict(enumerate(graph))
    group, coords, _ = port_block(g, double_cover(g), root, point)
    need(group.bit_count() == 2, "reference is only for a two-edge turn")
    return tuple(-2*(coords[v, 0] & (31 ^ group)).bit_count()
                 + 3*(coords[v, 0] & group).bit_count() for v in range(len(g)))


def literal_sampling(graph, root, point):
    # For length ell allocate |c_ell| copies of EACH of the 5^ell choices:
    # positive and negative channel count differences reproduce 40P exactly.
    weights = (-8, 5, 4, -1)
    plus, minus = Counter(), Counter()
    for length, w in enumerate(weights):
        destination = plus if w > 0 else minus
        for outcome, n in paths(graph, root, point, length).items():
            destination[outcome] += abs(w)*n
    total = sum(plus.values())+sum(minus.values())
    need(total == 258 and plus[None]+minus[None] > 0, "lost a path at the absorber")
    return tuple(plus[i]-minus[i] for i in range(len(graph))), total


def finite_time(graph, root, point, q):
    ev = basis(len(graph), point)
    odd = (0,)*len(graph)
    killed = 0
    hist = {}
    for time in range(65):
        need(sum(ev)+sum(odd)+killed == 6**time, "incorrect attempt denominator")
        if time in (0, 4, 8, 16, 32, 64):
            signed = [p-m for p, m in zip(ev, odd, strict=True)]
            max_error = max(abs(F(20*x, 4**time)-y) for x, y in zip(signed, q, strict=True))
            hist[time] = (max_error, F(sum(ev)+sum(odd), 6**time),
                          F(signed[point], 6**time))
            # For n>=1 the unretained eigenvalues have modulus < 15/4.
            need(max_error <= 20*F(15, 16)**time, "spectral margin")
        if time == 64:
            break
        ae, ao = step(graph, root, ev), step(graph, root, odd)
        killed = 6*killed+sum(ev[v]+odd[v] for v in graph[root])
        ev, odd = (tuple(x+y for x, y in zip(ev, ao, strict=True)),
                   tuple(x+y for x, y in zip(odd, ae, strict=True)))
    need(hist[64][0] < F(1, 2) and 20*F(15, 16)**64 < F(1, 2),
         "certified finite rounding in a SUPPLIED scale")
    return hist


def probe():
    graph = forced_completion()
    n = len(graph)
    checked, examples = Counter(), []
    for root in range(n):
        columns = []
        for point in range(n):
            if root == point:
                continue
            raw = basis(n, point)
            response = poly40(graph, root, raw)
            columns.append((point, response))
            need(step(graph, root, response) == tuple(-3*z for z in response)
                 and poly40(graph, root, response) == tuple(40*z for z in response),
                 "not an antialigned spectral projection")
            literal, starts = literal_sampling(graph, root, point)
            need(literal == response and starts == 258, "indexed vs literal outcomes")
            if point not in graph[root]:
                q = additive_reference(graph, root, point)
                need(response == tuple(2*z for z in q) and primitive(response) == q,
                     "untuned pulse differs from the supplied additive comparator")
                need(Counter(q) == {0: 1, 6: 1, -3: 2, 2: 3, -4: 3, 1: 6},
                     "charge histogram across the six classes")
                checked["two_step"] += 1
                if not examples:
                    examples.append(finite_time(graph, root, point, q))
            else:
                need(Counter(primitive(response)) != {0: 1, 6: 1, -3: 2, 2: 3, -4: 3, 1: 6},
                     "one-step mark should not give the two-step histogram")
                checked["one_step_control"] += 1
        by_point = dict(columns)
        need(all(by_point[u][v] == by_point[v][u] for u, v in product(by_point, repeat=2))
             and sum(col[u] for u, col in columns) == 160, "projector symmetry/rank four")
    need(checked == {"two_step": 160, "one_step_control": 80}, "missing frame")
    return checked, examples[0]


if __name__ == "__main__":
    counts, checkpoints = probe()
    print(dict(counts), "40P has rank four; a two-step pulse gives 2q at every vertex.")
    for n, (err, survive, signal) in checkpoints.items():
        print(f"ticks={n} max calibrated error={float(err):.5g}, "
              f"all-attempt survival={float(survive):.5g}, source contrast={float(signal):.5g}")
    print("Uniform 258-ticket comparison has expected contrast q/129; its length filter is graph-specific. "
          "No charge, event probability law, physical instrument or particle is derived.")
