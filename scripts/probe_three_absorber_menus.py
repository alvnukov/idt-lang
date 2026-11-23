"""Three selectable pairs of half-energy absorbers: what can local clicks tell us?

S4 here means the four-port reflection Sx = (sum(x)/2)1-x. A fixed input,
sign correction, two empty rails and setting-controlled lossless wiring give
each lit station the same ordered two-mode amplitude (1/2,1/2). They are
separate modes: square then add. This checks a finite field description,
not physical identity of hidden tags, timing, detector states or electronics.

Null: a uniform independently chosen pair exposes two stations. On a given
preparation each station's response to its half has a potential bit z_i,
independent of the current partner. Thresholds, backgrounds and readiness
can have arbitrary shared randomness and station dependence; stochastic
local noise may be included in the joint seed. This is a joint-response
hypothesis, stronger than equality of detected marginals or no signalling.
The bound holds in population, not in every finite realization of settings.
We count every preparation (zero/one/two clicks on the lit pair); the dark
station is not used as a veto. Dark-station clicks require a separate record.

The underlying triangle anticorrelation bound is known: Liang, Spekkens &
Wiseman, arXiv:1010.1273, Sec. II (original article with erratum). Here the
question is its half-energy implementation, sharp loss loophole and hidden
rail-provenance escape, not a new noncontextuality theorem or Bell experiment.
There are no experimental data, derived Born probabilities or spacetime claims.
"""

from __future__ import annotations

import json
from fractions import Fraction as F
from itertools import combinations, product

STATIONS = range(3)
PAIRS = tuple(combinations(STATIONS, 2))
BITS = tuple(product(range(2), repeat=3))
ROWS = tuple(product(range(2), repeat=2))  # (00,01,10,11) in fixed pair order


def need(ok, message):
    if not ok:
        raise ValueError(message)


def rail_controls():
    x = (1, 0, 0, 0)
    reflected = tuple(F(sum(x), 2) - v for v in x)
    need(reflected == (F(-1, 2), F(1, 2), F(1, 2), F(1, 2)), "four-port field")
    source = tuple(v * (-1 if i == 0 else 1) for i, v in enumerate(reflected)) + (0, 0)
    fields, provenance = {}, {}
    local = {i: set() for i in STATIONS}
    for a, b in PAIRS:
        off, = set(STATIONS) - {a, b}
        # Each six-slot operation is a permutation, not copying or attenuation.
        outputs = (2*a, 2*a+1, 2*b, 2*b+1, 2*off, 2*off+1)
        need(sorted(outputs) == list(range(6)), "nonreversible wire assignment")
        inv = tuple(outputs.index(j) for j in range(6))
        fields[a, b] = tuple((source[inv[2*i]], source[inv[2*i+1]]) for i in STATIONS)
        provenance[a, b] = tuple((inv[2*i], inv[2*i+1]) for i in STATIONS)
        for i, modes in enumerate(fields[a, b]):
            energy = sum(v*v for v in modes)
            need((energy, modes) == ((F(1, 2), (F(1, 2),)*2) if i in (a, b)
                                     else (0, (0, 0))), "unequal local amplitudes or energies")
            if i in (a, b):
                local[i].add(modes)
        # Setting-independent uniform seed selects one source rail. The tag
        # travels on it through the switch; local absorption receives the tag.
        # No knowledge of the setting is required when the seed is chosen.
        holders = [outputs[tag]//2 for tag in range(4)]
        need(holders.count(a) == holders.count(b) == 2, "causal one-particle control")
    need(all(len(s) == 1 for s in local.values()), "setting exposed by field coordinates")
    need(provenance[0, 1][1] != provenance[1, 2][1], "middle station should change input identity")
    # Impossible to keep a fixed pair of source rail identities at every lit
    # station: all distinct stations can be combined, hence require 6 rails.
    half_pairs = tuple(map(frozenset, combinations(range(4), 2)))
    need(not any(all(not c[i] & c[j] for i, j in PAIRS) for c in product(half_pairs, repeat=3)),
         "all three fixed provenance halves were pairwise disjoint")
    return {"mode_amplitudes_when_lit": ["1/2", "1/2"], "lit_energy": "1/2",
            "source_rails_at_B_in_AB": provenance[0, 1][1],
            "source_rails_at_B_in_BC": provenance[1, 2][1],
            "uniform_causal_tag_exact_one_fraction": "1"}


def distributions(mixture):
    """Unconditional joint bit probabilities for each separately selected pair."""
    need(all(w >= 0 and z in BITS for z, w in mixture) and sum(w for _, w in mixture) == 1,
         "invalid common hidden-bit distribution")
    return {edge: tuple(sum(w for z, w in mixture if (z[edge[0]], z[edge[1]]) == outcome)
                        for outcome in ROWS) for edge in PAIRS}


def measures(rows):
    avg = tuple(F(sum(row[i] for row in rows.values()), len(rows)) for i in range(4))
    zero, a, b, double = avg
    single = a + b
    return zero, single, double, single + 2*double


def symmetric_mixture(eta):
    """Attains minimal lit-pair doubles at each fixed mean 0 <= eta <= 1."""
    eta = F(eta)
    need(0 <= eta <= 1, "target router efficiency outside 0..1")
    if eta <= F(2, 3):
        masses = (1 - 3*eta/2, 3*eta/2, 0)
    else:
        masses = (0, 2 - 3*eta/2, 3*eta/2 - 1)
    return [(z, F(masses[sum(z)], (1, 3, 3)[sum(z)])) for z in BITS if sum(z) <= 2]


def graph_bound(weights):
    """Weighted max-cut is just the best deterministic one-click frequency."""
    n = 1 + max(max(edge) for edge in weights)
    total = sum(weights.values())
    return max(F(sum(w for (i, j), w in weights.items() if z[i] != z[j]), total)
               for z in product((0, 1), repeat=n))


def probe():
    rail = rail_controls()
    vertices = {}
    for z in BITS:
        rows = distributions([(z, 1)])
        zero, single, double, eta = measures(rows)
        # All mixtures obey these linear inequalities. A Boolean assignment
        # crosses 0 or 2 of the 3 edges, never all 3. Eta is mean click count,
        # NOT accepted fraction when doubles occur: eta = P1 + 2 P2.
        need(single <= F(2, 3) and double >= max(0, eta/2-F(1, 3)),
             "triangle single/double bound")
        vertices[sum(z)] = tuple(map(str, (zero, single, double, eta)))
    need(len(vertices) == 4, "missing shared-color vertices")
    tested = {F(p, q) for q in range(1, 21) for p in range(q+1)}
    examples = {}
    for eta in sorted(tested):
        rows = distributions(symmetric_mixture(eta))
        loss = max(0, eta/2-F(1, 3))
        expected = (1-eta+loss, eta/2-loss, eta/2-loss, loss)
        router = (1-eta, eta/2, eta/2, 0)
        need(all(row == expected for row in rows.values()), "not a symmetric sharp construction")
        need(measures(rows)[2:] == (loss, eta), "countercontrol lost its target mean")
        need((expected == router) == (eta <= F(2, 3)), "lossy router agreement boundary")
        # On every row TV >= difference in one-click probability. This uniform
        # construction attains the lower bound on the average of the row TVs:
        # max(0,eta-2/3), even if competitors may choose another mean.
        tv = sum(abs(a-b) for a, b in zip(expected, router, strict=True))/2
        need(tv == max(0, eta-F(2, 3)), "sharp unconditional joint-table TV")
        if eta in (F(1, 2), F(2, 3), F(3, 4), F(1)):
            examples[str(eta)] = {"row_00_01_10_11": list(map(str, expected)),
                                  "double": str(loss), "mean_row_TV_to_router": str(tv)}
    # A stationary local threshold realization needs no independent noise: set
    # threshold 1/4 on marked stations, 3/4 on the others, click if E >= T.
    for z in BITS:
        t = tuple(F(1, 4) if bit else F(3, 4) for bit in z)
        need(tuple(int(F(1, 2) >= v) for v in t) == z and all(0 < v for v in t),
             "thresholds must realize the joint bits with no dark clicks")
    def cycle(n):
        return {(i, (i+1) % n): 1 for i in range(n)}

    graph = {n: graph_bound(cycle(n)) for n in (3, 4, 5)}
    biased = graph_bound({(0, 1): 8, (1, 2): 1, (0, 2): 1})
    need((graph[3], graph[4], graph[5], biased) == (F(2, 3), 1, F(4, 5), F(9, 10)),
         "weighted graph controls; independence does not imply uniformity")
    # Allowing the two local outputs to have arbitrary partner-specific joint
    # noise also permits perfect anticorrelation with identical fair marginals.
    # This cannot be one common triple of bits; it is not in the threshold null.
    pair_only = {edge: (0, F(1, 2), F(1, 2), 0) for edge in PAIRS}
    need(measures(pair_only) == (0, 1, 0, 1) and
         all(r[1] + r[3] == r[2] + r[3] == F(1, 2) for r in pair_only.values()),
         "identical local marginals are not a sufficient joint-response test")
    return {"fixture": rail, "population_scope": "uniform independent pair; all preparations; "
            "no need for iid detectors, but one jointly coupled partner-independent response per station",
            "one_click_bound": "2/3", "min_double_at_fixed_mean_eta_0_to_1": "max(0,eta/2-1/3)",
            "sharp_router_TV": "max(0,eta-2/3)", "vertices_by_number_hot_00gap_P1_P2_mean": vertices,
            "sharp_loss_examples": examples, "fractions_replayed": len(tested),
            "uniform_cycles": {n: str(v) for n, v in graph.items()}, "biased_triangle": str(biased),
            "limitations": "Field matching is not ontic matching. A tagged causal carrier produces "
            "one click per ideal run; thinning it realizes the exclusive router at any efficiency. "
            "Setting leakage or joint pair-dependent noise also evades the bit bound. No physical "
            "calibration, herald record, crosstalk bound or significance supplied."}


if __name__ == "__main__":
    print(json.dumps(probe(), sort_keys=True))
