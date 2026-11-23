"""Five compatible alternatives in the scheduled ternary one-token apparatus.

Run: python3 -B -m scripts.probe_native_pentagon_contexts [--json]

Each fixed event routes the raw data, copies one port's T predicate into
ordinary blank records, and undoes the route. A pair acts on ONE prepared
stock with separate records. This is a finite, supplied detector schedule,
not autonomous detection. No amplitude or probability rule enters the contact
replay. Source mixtures, settings, initialized stock and addressing are inputs.

The two versions of event i are L_i in context (i-1,i) and R_i in (i,i+1).
For a deterministic common coupling put S=sum(L+R)/2, D=sum[L!=R], and
J=sum_i R_i L_(i+1). There are S-D/2 vertices with two yes values. For each
edge internal to those vertices delete one of its ends; there are at most J
such edges. What remains is independent in a pentagon, hence has size <=2.
Thus S<=2+D/2+J, also in expectation. All ten-bit assignments are checked.
D is a same-stock quantity in a proposed coupling, not an outcome of a
physical trial in incompatible alternative contexts. Equal event marginals
do not determine it. Even the full five edge distributions need not do so.

Klyachko et al., https://arxiv.org/abs/0706.0126, Eq. (8): the external
regular pentagram has axial Born probability 1/sqrt(5) for each ray.
This is a single-system contextuality comparison, not a Bell experiment.
For why imperfect sequential compatibility matters, see Gühne et al.,
https://doi.org/10.1103/PhysRevA.81.022121. We import no experimental
counts, no physical compatibility/efficiency assumption and no new status.
The separate probe_native_rational_pentagon.py supplies sharp projective
readout and amplitudes; its 13/6 is not a ternary-contact result.
"""

import argparse
from collections import Counter, defaultdict, deque
from fractions import Fraction
from functools import cache
from itertools import combinations, product
import json
from math import cos, pi, sin, sqrt

from scripts import probe_ternary_active_readout as active
from scripts import probe_ternary_vacancy_switch as vacancy
from scripts.probe_eight_label_interferometer import check

AB, BC, CA = (0, 1), (1, 2), (2, 0)
STOCKS = tuple(product(range(3), product(range(2), repeat=3)))
EVENTS = (((), 0), ((), 1), ((CA,), 0), ((BC, CA), 2), ((BC,), 1))
CAT = 9  # Three data sites, each accompanied by its own pair of control sites.


def _raw(stock):
    source, bits = stock
    return tuple(x for i in range(3)
                 for x in ("T" if source == i else "N", *vacancy.stock(bits[i])))


@cache
def _route(hubs):
    return tuple(edge for a, b in hubs for i, j in vacancy.switch(a, b, 3)
                 for edge in active.mapped(active.VACANCY, (i, j, CAT)))


def _read(stock, queries):
    data = tuple(active.RECODE[x] for x in _raw(stock)) + ("a",)
    state = list(data + ("b", "b") * len(queries))
    for k, (hubs, port) in enumerate(queries):
        route = _route(hubs)
        r = CAT + 1 + 2 * k
        for edge in route:
            active.step(state, edge)
        routed = tuple(state[:CAT+1])
        for edge in active.mapped(active.PROTECTED_METER, (3*port, r, r+1, CAT)):
            active.step(state, edge)
        check(tuple(state[:CAT+1]) == routed, "protected read changed a routed stock")
        for edge in reversed(route):
            active.step(state, edge)
        check(tuple(state[:CAT+1]) == data, "inverse route did not restore the input stock")
    pairs = tuple(zip(state[CAT+1::2], state[CAT+2::2], strict=True))
    check(all(pair in (("a", "a"), ("b", "b")) for pair in pairs), "invalid copy")
    return tuple(int(a == "a") for a, _ in pairs)


def read_pair(stock, i, j):
    return _read(stock, (EVENTS[i], EVENTS[j]))


def native_witness():
    rows = {}
    for stock in STOCKS:
        pairs = tuple(read_pair(stock, i, (i+1) % 5) for i in range(5))
        clicks = tuple(a for a, _ in pairs)
        for i, (a, b) in enumerate(pairs):
            j = (i+1) % 5
            check(b == clicks[j] and not a*b, "context identity or exclusivity failed")
            check(read_pair(stock, j, i) == (b, a), "reversing read order changed a record")
            k = (i+2) % 5
            check(read_pair(stock, i, k) == (a, clicks[k]), "diagonal read changed a record")
        rows[stock] = clicks
    # The five different two-hit preparations are concrete, not invented valuations.
    witnesses = []
    for i in range(5):
        found = next((s for s, v in rows.items() if v[i] and v[(i+2) % 5]), None)
        check(found is not None, "missing co-clickable diagonal")
        witnesses.append(found)
    histogram = Counter(map(sum, rows.values()))
    hits = [sum(rows[s][i] for s in witnesses) for i in range(5)]
    edge_counts = [[0]*4 for _ in range(5)]
    for s, i in product(witnesses, range(5)):
        a, b = read_pair(s, i, (i+1) % 5)
        edge_counts[i][2*a+b] += 1
    check(histogram == {1: 8, 2: 16} and hits == [2]*5, "wrong native stock census")
    return {"score_histogram_over_24": dict(histogram), "exclusive_edges": 5,
            "co_clickable_diagonals": 5, "symmetric_stock_count": len(witnesses),
            "symmetric_stocks_source_bits": witnesses, "symmetric_hits_per_event": hits,
            "symmetric_edge_counts": edge_counts}


def frame_closure():
    """Compare a stricter detector: both ports read after just ONE shared route.

    Close under all words of the three frozen hubs on these 24 stocks. This is
    not closure under every possible ternary contact word or detector schedule.
    """
    index = {_raw(s): k for k, s in enumerate(STOCKS)}
    generators = []
    for a, b in (AB, BC, CA):
        word = vacancy.switch(a, b, 3)
        generators.append(tuple(index[vacancy.replay(_raw(s), word)[-1]] for s in STOCKS))
    identity = tuple(range(len(STOCKS)))
    seen, todo, adj = {identity}, deque([identity]), defaultdict(set)
    while todo:
        frame = todo.popleft()
        masks = [sum(1 << i for i, x in enumerate(frame) if STOCKS[x][0] == port)
                 for port in range(3)]
        for a, b in combinations(masks, 2):
            adj[a].add(b)
            adj[b].add(a)
        for g in generators:
            out = tuple(g[x] for x in frame)
            if out not in seen:
                seen.add(out)
                todo.append(out)

    def faithful(path):
        if len(path) == 5:
            return (path[0] in adj[path[-1]]
                    and all(path[i] & path[(i+2) % 5] for i in range(5)))
        return any(faithful((*path, node)) for node in adj[path[-1]]
                   if node not in path and (len(path) < 2 or node & path[-2]))

    return {"maps": len(seen), "events": len(adj), "coframe_pairs": sum(map(len, adj.values()))//2,
            "all_disjoint_pairs": sum(not a & b for a, b in combinations(adj, 2)),
            "faithful_cycles_exist": any(faithful((node,)) for node in adj)}


def score(left, right):
    return (Fraction(sum(left) + sum(right), 2), sum(a != b for a, b in zip(left, right, strict=True)),
            sum(right[i] * left[(i+1) % 5] for i in range(5)))


def edge_controls(alternating):
    """A supplied context-sensitive address controller, not an emergent source.

    Each edge reads the occupied and a blank port on the same native stock.
    Five rotations and two mirrored orientations determine which address is
    labeled as which event; settings do not change their sampling weights.
    Edge table order: 00, 01, 10, 11. No records or trials are discarded.
    """
    base = (1, 0, 1, 0, 1) if alternating else (1, 1, 1, 1, 1)
    counts, defects = [[0]*4 for _ in range(5)], []
    for shift, mirror in product(range(5), (False, True)):
        left, right = [0]*5, [0]*5
        for i in range(5):
            bit = 1-base[(shift-i) % 5] if mirror else base[(i-shift) % 5]
            a, b = _read(STOCKS[0], (((), 1-bit), ((), bit)))
            right[i], left[(i+1) % 5] = a, b
            counts[i][2*a+b] += 1
        s, d, j = score(left, right)
        check(s == Fraction(5, 2) and j == 0, "wrong context-control edge readout")
        defects.append(d)
    expected = 1 if alternating else 5
    check(defects == [expected]*10 and counts == [[0, 5, 5, 0]]*5, "wrong control ensemble")
    return {"mean_D": expected, "edge_counts": counts}


def external_target():
    """Born/rank-one witness ONLY: p=cos(pi/5)/(1+cos(pi/5))=1/sqrt(5).

    Azimuth step 4*pi/5 makes the neighboring dot product p-(1-p)*cos(pi/5).
    Mixing the native symmetric stock and the supplied alternating control
    with w=2*sqrt(5)-4 gives each ideal edge law (1-2p,p,p,0).
    At J=0 the inequality forces mean D>=2*(sqrt(5)-2); this coupling
    attains it. Using the constant instead gives the SAME edges with D=5w.
    This is a constructed simulation, not a prediction or experimental fit.
    """
    p = 1/sqrt(5)
    rays = [(sqrt(1-p)*cos(4*pi*i/5), sqrt(1-p)*sin(4*pi*i/5), sqrt(p)) for i in range(5)]
    dot = max(abs(sum(x*y for x, y in zip(ray, rays[(i+1) % 5], strict=True)))
              for i, ray in enumerate(rays))
    return {"score": sum(ray[2]**2 for ray in rays), "max_adjacent_abs_dot": dot,
            "contextual_mixture_weight": 2*sqrt(5)-4, "per_event": p}


def verify():
    scores = [score(vals[:5], vals[5:]) for vals in product((0, 1), repeat=10)]
    check(all(2*s <= 4+d+2*j for s, d, j in scores), "assignment violated defect bound")
    check({(2, 0, 0), (Fraction(5, 2), 1, 0), (3, 0, 1)} <= set(scores),
          "constant, mismatch or joint-hit coefficient not witnessed sharply")
    native = native_witness()
    alternating, constant = edge_controls(True), edge_controls(False)
    reference = external_target()
    w = reference["contextual_mixture_weight"]
    # The two coefficients of (1-w), w are exact rational raw edge frequencies.
    fixed, switched = native["symmetric_edge_counts"], alternating["edge_counts"]
    check(fixed == [[1, 2, 2, 0]]*5 and switched == constant["edge_counts"],
          "mixtures do not share the required complete tables")
    mixed = [[(1-w)*a/sum(f) + w*b/sum(s) for a, b in zip(f, s, strict=True)]
             for f, s in zip(fixed, switched, strict=True)]
    couplings = {"minimum_mean_D": w*alternating["mean_D"], "alternative_mean_D": w*constant["mean_D"],
                 "five_edge_probabilities_00_01_10_11": mixed}
    return {"potential_assignments": len(scores), "native": native, "single_frame": frame_closure(),
            "alternating": alternating, "constant": constant, "supplied_qutrit_reference": reference,
            "target_couplings": couplings,
            "boundary": "finite full-stock replay; counterfactual D is not measured by edge marginals; "
                        "contextual addressing, preparation changes or postselection can evade the raw bound"}


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    parser.add_argument("--json", action="store_true")
    args = parser.parse_args()
    print(json.dumps(verify(), indent=None if args.json else 2))
