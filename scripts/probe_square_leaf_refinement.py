"""Square leaf counts from exact equal-wave contact circuits.

An equal contact of degree d acts by y_i=(2/d)*sum(x)-x_i. On an
isolated signed amplitude m (integer magnitude m>0), degree 2m leaves
one opposite residual of magnitude m-1 and 2m-1 unit outputs. Repeat
on the residual: m-1 contacts and m² unit leaves. These are staged
orthogonal gates on one branch plus blank modes. A passive undirected
tree with uncontrolled reflected re-entry is not this schedule.

There is also an exact least maximum degree for isolated magnitude
m>1, when all degrees up to the cap are allowed. A missing prime p|m
stays a common divisor in the ring with only the permitted denominator
primes inverted. With degree at most three, the gate is a swap at d=2
and the identity modulo two at d=3, so the number of odd coordinates
cannot grow from zero or one to m². Thus the cap is at least both four
and the greatest prime factor of m. For the matching upper bound,
split a factor of two using degree four; an odd prime p has a degree-p
split into magnitudes p−2 and p−1 copies of two (times the common
remaining scale), after which all new factors are smaller than p.
These modular obstructions still hold if wires are permuted or signs
flipped, but not if extra waves or arbitrary rescalings are supplied.

This gives a conditional event derivation only. Supply blank-mode
extension, exactly one registered leaf, interchange symmetry of the
complete operational preparations (including phases and branch
records), and consistency of local refinement and discarding the leaf
address. Then equiprobable leaves group in counts a_i² for a normalized
rational input a_i/q. The contact calculation supplies no such
event, detector rule, or history erasure. There is no claim here for
arbitrary irrational amplitudes or convergence of a detector law.

The structural comparison is Zurek, arXiv:quant-ph/0405161, §§II.D
and V.B: his separate construction supplies correlated Schmidt
records and envariant swaps, not an equal-wave Kirchhoff gate.
"""

from __future__ import annotations

import json
from collections import Counter
from dataclasses import dataclass, field
from fractions import Fraction as F
from itertools import combinations
from math import ceil

MAX_LEAVES = 4096


def need(ok, why):
    if not ok:
        raise ArithmeticError(why)


def scatter(v):
    d = len(v)
    need(d >= 2, "requires a contact of degree at least two")
    center = F(2*sum(v), d)
    return tuple(center-x for x in v)


@dataclass
class Circuit:
    source: tuple[int, ...]
    values: list[int] = field(init=False)
    owner: list[int] = field(init=False)
    log: list[tuple[int, ...]] = field(default_factory=list, init=False)

    def __post_init__(self):
        need(all(type(x) is int for x in self.source)
             and 0 < sum(x*x for x in self.source) <= MAX_LEAVES,
             "integer branch sources exceed the checked leaf budget or are all zero")
        self.values = list(self.source)
        self.owner = list(range(len(self.source)))

    def contact(self, p: int, degree: int) -> tuple[int, ...]:
        a = self.values[p]
        group = self.owner[p]
        need(a != 0 and type(degree) is int and degree >= 2, "unexpected empty branch or degree")
        first = len(self.values)
        indices = (p, *range(first, first+degree-1))
        x = (a,)+(0,)*(degree-1)
        y = scatter(x)
        need(all(v.denominator == 1 for v in y), "refinement used a nonintegral scaled voltage")
        need(sum(y) == sum(x) and sum(t*t for t in y) == a*a and scatter(y) == x,
             "contact failed signed-sum, squared norm or inverse check")
        self.values[p] = int(y[0])
        self.values.extend(map(int, y[1:]))
        self.owner.extend([group]*(degree-1))
        self.log.append(indices)
        return indices

    def verify_inverse(self):
        state = list(self.values)
        for ports in reversed(self.log):
            recovered = scatter(tuple(state[i] for i in ports))
            need(all(v.denominator == 1 for v in recovered), "nonintegral inverse on a staged output")
            for p, v in zip(ports, recovered, strict=True):
                state[p] = int(v)
        need(state == [*self.source, *([0]*(len(state)-len(self.source)))],
             "full wave circuit did not undo branch extension into its initially blank modes")


def unrestricted(assembly: Circuit, mode: int):
    """Use decreasing degree 2m, with the residual travelling to the next gate."""
    while (m := abs(assembly.values[mode])) > 1:
        ports = assembly.contact(mode, 2*m)
        need(abs(assembly.values[ports[0]]) == m-1
             and all(abs(assembly.values[p]) == 1 for p in ports[1:]), "expected one residual and 2m-1 leaves")


def prime_factors(m: int) -> tuple[int, ...]:
    need(m > 0, "factorization of a positive magnitude expected")
    factors = []
    d = 2
    while d*d <= m:
        while m % d == 0:
            factors.append(d)
            m //= d
        d += 1
    if m > 1:
        factors.append(m)
    return tuple(factors)


def bounded(assembly: Circuit, mode: int, factor: int, scale: int = 1) -> tuple[int, ...]:
    """Factor refinement using no arity above max(4, largest prime factor)."""
    need(abs(assembly.values[mode]) == factor*scale, "wrong magnitude for factor refinement")
    if factor == 1:
        return (mode,)
    p = prime_factors(factor)[-1]
    block = factor//p
    unit = block*scale
    if p == 2:
        leaves = assembly.contact(mode, 4)
    else:
        # For p=3 the residual is already one unit; for p>=5 it
        # factors strictly below p. The p-1 new outputs have size two.
        residual, *twos = assembly.contact(mode, p)
        leaves = bounded(assembly, residual, p-2, unit)
        for child in twos:
            leaves += bounded(assembly, child, 2, unit)
    need(len(leaves) == p*p and all(abs(assembly.values[v]) == unit for v in leaves), "prime factor split")
    return tuple(out for leaf in leaves for out in bounded(assembly, leaf, block, scale))


def synthesize(source: tuple[int, ...], method: str) -> Circuit:
    circuit = Circuit(source)
    for i, m in enumerate(map(abs, source)):
        if not m:
            continue  # empty label survives; no filled leaf is removed
        if method == "unrestricted":
            unrestricted(circuit, i)
        else:
            need(method == "least_max_valence", "unknown refinement policy")
            emitted = bounded(circuit, i, m)
            need(len(set(emitted)) == len(emitted) == m*m
                 and all(circuit.owner[p] == i for p in emitted), "wrong factor branch bookkeeping")
    circuit.verify_inverse()
    return circuit


def census(circuit: Circuit) -> dict[str, object]:
    expected = {i: m*m for i, m in enumerate(circuit.source)}
    sizes = Counter(i for p, i in enumerate(circuit.owner) if circuit.values[p])
    signs = Counter((i, circuit.values[p]) for p, i in enumerate(circuit.owner) if circuit.values[p])
    need(all(abs(x) <= 1 for x in circuit.values) and all(sizes[i] == expected[i] for i in expected),
         "nonunit output or wrong group leaf count")
    for i, a in enumerate(circuit.source):
        # All equal magnitude outputs still need not have equal signs.
        need(signs[i, 1] == (a*a+a)//2 and signs[i, -1] == (a*a-a)//2,
             "branch signed sum not preserved")
    return {"contacts": len(circuit.log),
            "maximum_arity": max(map(len, circuit.log), default=0),
            "occupied_leaves_by_branch": [sizes[i] for i in expected],
            "positive_and_negative_leaves_by_branch": [[signs[i, 1], signs[i, -1]] for i in expected],
            "blank_exposed_modes": circuit.values.count(0),
            "orders_of_contacts": dict(sorted(Counter(map(len, circuit.log)).items()))}


def valence_research() -> list[dict[str, object]]:
    entries = []
    for m in (1, 2, 3, 4, 5, 6, 7, 8, 9, 11, 12, 15, 18):
        wide = census(synthesize((m,), "unrestricted"))
        local = census(synthesize((m,), "least_max_valence"))
        degree = max(4, *prime_factors(m)) if m > 1 else 0
        need(wide["contacts"] == m-1 and wide["maximum_arity"] == (2*m if m > 1 else 0),
             "decreasing residual split was not linear in m")
        need(local["maximum_arity"] == degree, "unexpected factor construction cap")
        # One gate meeting at least one occupied port can create no
        # more occupied outputs than its degree, thus add at most d-1.
        lower = ceil(F(m*m-1, degree-1)) if degree else 0
        need(local["contacts"] >= lower, "support-production lower bound")
        entries.append({"isolated_integer_amplitude": m, "unrestricted_contacts": wide["contacts"],
                        "unrestricted_max_degree": wide["maximum_arity"], "least_max_degree": degree,
                        "contacts_at_minimal_degree_cap": local["contacts"],
                        "support_only_node_lower_bound_at_that_cap": lower,
                        "attains_support_lower_bound": local["contacts"] == lower})
    # For the original pair d=3,4, all rational gate entries have
    # denominators prime to 5. That ring ideal 5R is invariant under
    # every such gate, so an isolated 5 cannot make even one ±1.
    for d in (2, 3, 4):
        for p in range(d):
            entries_of_gate_column = scatter(tuple(int(i == p) for i in range(d)))
            need(all(x.denominator % 5 and (5*x).numerator % 5 == 0 for x in entries_of_gate_column),
                 "bounded alphabet does not preserve the stated modular obstruction")
            if d in (2, 3):
                odd_sites = tuple(i for i, x in enumerate(entries_of_gate_column)
                                  if x.denominator % 2 and x.numerator % 2)
                need(all(x.denominator % 2 for x in entries_of_gate_column)
                     and odd_sites == ((1-p,) if d == 2 else (p,)), "degree-two/three parity map")
    return entries


def normalized_examples():
    s3_output = scatter((1, 0, 0))
    need(s3_output == (F(-1, 3), F(2, 3), F(2, 3)), "S3 input control")
    examples = {
        "S3_from_one_occupied_input": (tuple(int(3*v) for v in s3_output), 3),
        "same_ray_unreduced_denominator": ((-2, 4, 4), 6),
        "Pythagorean_with_blank_branch": ((3, -4, 0), 5),
        "four_nonzero_branches": ((1, -2, 2, 4), 5),
        "prime_admissibility_control": ((5, -12, 0), 13),
    }
    result = {}
    for label, (a, q) in examples.items():
        need(sum(v*v for v in a) == q*q, "example not a normalized rational state")
        data = census(synthesize(a, "least_max_valence"))
        need(sum(data["occupied_leaves_by_branch"]) == q*q, "not q² equal-magnitude leaves")
        result[label] = {"integer_amplitudes": a, "q": q, "amplitude_magnitude": str(F(1, q)),
                         "total_occupied_leaves": q*q, "branch_leaf_circuit": data,
                         "grouped_weights_given_equal_exclusive_leaf_events": [
                             str(F(n, q*q)) for n in data["occupied_leaves_by_branch"]
                         ]}
    need(result["S3_from_one_occupied_input"]["branch_leaf_circuit"]["contacts"] == 2
         and result["S3_from_one_occupied_input"]["branch_leaf_circuit"]["orders_of_contacts"] == {4: 2},
         "S3 example is not exactly two extra four-port gates")
    need(result["S3_from_one_occupied_input"]["grouped_weights_given_equal_exclusive_leaf_events"]
         == result["same_ray_unreduced_denominator"]["grouped_weights_given_equal_exclusive_leaf_events"]
         == ["1/9", "4/9", "4/9"], "q rescaling unexpectedly changed grouped weights")
    return result


def event_controls():
    circuit = synthesize((-1, 2, 2), "least_max_valence")
    signed_swaps = ordinary_swaps = 0
    for i, j in combinations(range(len(circuit.values)), 2):
        trial = circuit.values[:]
        trial[i], trial[j] = trial[j], trial[i]
        if trial != circuit.values:
            trial[i], trial[j] = -trial[i], -trial[j]
            signed_swaps += 1
        else:
            ordinary_swaps += 1
        need(trial == circuit.values, "equal-magnitude exposed leaves not interchangeable up to signs")
    need((ordinary_swaps, signed_swaps) == (18, 18), "unexpected S3 pair symmetry counts")
    # Both controls keep the exact same linear wave amplitudes.
    # Tag-weighted leaf events are still exclusive and normalizable;
    # their symmetry only permutes leaves *inside* an original group.
    branch_tag_weights = (F(1), F(0), F(0))
    counts = Counter(circuit.owner)
    tag_events = tuple(branch_tag_weights[i]/counts[i] for i in circuit.owner)
    need(sum(tag_events) == 1, "tagged ensemble not normalized")
    # Detector efficiency 1/2 on one branch only. Raw trial totals
    # include the no-click outcome; conditioning alters the ratios.
    efficiency = (F(1), F(1, 2), F(1))
    raw = tuple(F(counts[i], 9)*efficiency[i] for i in range(3))
    loss = 1-sum(raw)
    conditional = tuple(p/sum(raw) for p in raw)
    need(raw == (F(1, 9), F(2, 9), F(4, 9)) and loss == F(2, 9)
         and conditional == (F(1, 7), F(2, 7), F(4, 7)), "loss/postselection control")
    return {
        "all_exposed_leaf_swaps_can_preserve_the_amplitude_vector_with_local_phase_compensation": True,
        "ordinary_leaf_swaps_fixing_S3_refined_vector": ordinary_swaps,
        "opposite_sign_leaf_swaps_requiring_pair_sign_compensation": signed_swaps,
        "retained_branch_tag_countercontrol": {
            "same_amplitudes_exclusive_normalized_events": True,
            "group_weights": list(map(str, branch_tag_weights)),
            "violates": "equiprobability across branch histories, not local within-group symmetry",
        },
        "one_branch_half_efficiency_countercontrol": {
            "raw_group_clicks": list(map(str, raw)), "no_click": str(loss),
            "incorrect_comparison_if_conditioned_on_a_click": list(map(str, conditional)),
        },
    }


def probe():
    return {
        "scope": "exact staged amplitude refinement plus conditional coarse event bookkeeping; no physical inference",
        "normalized_examples": normalized_examples(),
        "isolated_integer_resource_examples": valence_research(),
        "resource_boundary": {
            "least_maximum_degree_when_all_valences_up_to_cap_allowed": "max(4, largest prime factor(m)), m>1",
            "lower_bound_argument": "a missing prime remains a divisor of every output; d<=3 preserves parity support",
            "constructive_upper_bound": "split prime factors; odd prime p first sends p to -(p-2) and (p-1) copies of two",
            "only_degrees_3_and_4": "multiplicative refinements for 2^a 3^b; isolated m=5 impossible over Z[1/6]",
        },
        "event_controls": event_controls(),
        "supplied": [
            "local synchronous blank inputs; separate branch routing with no unregistered re-entry",
            "signed swap symmetry of the entire relevant state and instrument, not only the amplitude list",
            "exclusive registering trial with known denominator; unbiased leaf detection and blank-mode consistency",
            "branch marginal unchanged by refinement and the calibrated act of forgetting the leaf label",
        ],
        "primary_comparison": {
            "source": "https://ar5iv.labs.arxiv.org/html/quant-ph/0405161#S2.SS4",
            "doi": "10.1103/PhysRevA.71.052105",
            "use": "compare equal fine outcomes and grouping only; Zurek uses envariant swaps of entangled Schmidt records",
        },
    }


if __name__ == "__main__":
    print(json.dumps(probe(), sort_keys=True, separators=(",", ":")))
