"""Serial and repeated-pair tests of the frozen mobile-blank splitter.

Run: python3 -m scripts.probe_vacuum_compensated_network [--json]
All primary rows are raw scheduled contacts, counting the token on BOTH
cells of each port. Hidden shades are sampled at launch, never between gates.
Pure three-mode amplitudes and fresh coins are separate comparison models.
"""

import argparse
from collections import Counter
from fractions import Fraction
from functools import cache
from itertools import combinations, product
import json

from scripts import probe_mobile_blank_interferometer as mobile
from scripts.probe_eight_label_interferometer import check

AB, BC, CA = (0, 1), (1, 2), (2, 0)
CHAIN = (AB, BC)
TRIANGLE = (*CHAIN, CA)
REPEATED = (*CHAIN, AB)
SHADES = (1, 2)
LABELS = (1, 2, 3)
# Existing splitter layout (D,E,Z,D,E,Z); add separate fresh-1 sites 6,7.
FLIP_D = (((2, 0), (5, 3)),)
PRE_SWAP = (((0, 1), (3, 4)),)
VIA_SCRATCH = (((0, 6), (3, 7)), ((1, 0), (4, 3)), ((6, 1), (7, 4)))
WORDS = {"S": mobile.SPLITTER, "F": mobile.SPLITTER + FLIP_D,
         "U": mobile.SPLITTER + FLIP_D + PRE_SWAP + VIA_SCRATCH}


@cache
def device(arms, variant):
    """Replay fixed contacts on both rails; ignore only verified clean leaves."""
    initial = (*arms[0], 0, *arms[1], 0, 1, 1)
    trace = mobile._replay(initial, WORDS[variant])
    check(all(state[2] == state[5] == 0 for state in trace.states), "dirty zero leaf")
    check(trace.output[6:] == (1, 1), "scratch not restored")
    return mobile._rails(trace.output)


def counts(variant, edges):
    rows = []
    for source in range(3):
        row = [0, 0, 0]
        for shades in product(SHADES, repeat=3):
            rails = [(3 if i == source else 1, e) for i, e in enumerate(shades)]
            for a, b in edges:
                rails[a], rails[b] = device((rails[a], rails[b]), variant)
            read = [pair.count(3) for pair in rails]
            check(sum(read) == 1, "raw detector accounting")
            row = [x + y for x, y in zip(row, read, strict=True)]
        rows.append(tuple(row))
    return tuple(rows)


def fresh_counts(edges):
    """Denominator 2**len(edges); independent fair choice on EVERY contact."""
    rows = []
    for source in range(3):
        row = [0, 0, 0]
        for bits in product((0, 1), repeat=len(edges)):
            slot = source
            for (a, b), swap in zip(edges, bits, strict=True):
                if swap and slot in (a, b):
                    slot = b if slot == a else a
            row[slot] += 1
        rows.append(tuple(row))
    return tuple(rows)


def crossing_kernel():
    """Counts over fair vacant D for each occupied E, vacant E in {1,2}."""
    return tuple(tuple(sum(device(((3, e), (d, g)), "S")[1].count(3) for d in SHADES)
                       for g in SHADES) for e in SHADES)


def audit_devices():
    """Exhaust the 81 positive-label inputs, not just the one-token code."""
    squares = vacua = code = 0
    outputs = set()
    for d, e, f, g in product(LABELS, repeat=4):
        raw = ((d, e), (f, g))
        out = device(raw, "U")
        outputs.add(out)
        squares += device(out, "U") == raw
        if 3 not in (d, e, f, g):
            check(device(raw, "S") == ((3-d, e), (3-f, g)), "vacuum flip law")
            check(device(raw, "F") == out == raw, "pointwise vacuum correction")
            vacua += 1
        if {d, f} == {1, 3} and e in SHADES and g in SHADES:
            expected = ((f, e), (d, g)) if e != g else raw
            check(out == expected and device(out, "U") == raw, "static XOR code law")
            code += 1
    check((len(outputs), squares, vacua, code) == (81, 63, 16, 8), "device coverage")
    for d, e in product(LABELS, repeat=2):
        via = (((0, 2),), ((1, 0),), ((2, 1),))
        check(mobile._replay((d, e, 1), via).output == (e, d, 1), "native swap")
    check(crossing_kernel() == ((0, 2), (1, 0)), "stationary stock crossing law")
    return {"operating_states": len(outputs), "vacuum_fixed": vacua,
            "one_token_code": code, "square_fixed": squares}


def two_arm():
    """New U uses an E flip plate and D=1 refill; dump both raw cells."""
    trials = {}
    for source, plates, opened in mobile.SETTINGS:
        row = [0, 0, 0]
        for seeds, fills in product(mobile.SEEDS, repeat=2):
            raw = tuple((3 if i == source else 1, e) for i, e in enumerate(seeds))
            split = device(raw, "U")
            incoming, dumps = [], []
            for i, (d, e) in enumerate(split):
                plated = mobile._replay((d, e, 0), (((2, 1),),) if plates[i] else ()).output
                check(plated == (d, 3-e if plates[i] else e, 0), "late plate")
                old = plated[:2]
                fill = (1, fills[i])
                closed = mobile._replay((*old, 1, 1, *fill), () if opened[i] else mobile.SHUTTER)
                expected = (*old, 1, 1, *fill) if opened[i] else (*fill, *old, 1, 1)
                check(closed.output == expected, "raw dump/refill")
                incoming.append(closed.output[:2])
                dumps.append(closed.output[2:4])
            out = device(tuple(incoming), "U")
            outcome = (*[pair.count(3) for pair in out], sum(pair.count(3) for pair in dumps))
            check(sum(outcome) == 1, "dump-inclusive accounting")
            row = [x+y for x, y in zip(row, outcome, strict=True)]
            trials[source, plates, opened, seeds, fills] = (incoming, dumps, outcome)
        check(tuple(row) == mobile._expected(source, plates, opened), "shutter/plate row")
    erases = 0
    for (source, plates, opened, seeds, fills), (incoming, dumps, outcome) in trials.items():
        for i in range(2):
            if not opened[i] and not plates[i]:
                toggled = tuple(flag or j == i for j, flag in enumerate(plates))
                other_in, other_dumps, other_out = trials[source, toggled, opened, seeds, fills]
                check((incoming, outcome) == (other_in, other_out) and
                      dumps[i] != other_dumps[i] and dumps[1-i] == other_dumps[1-i],
                      "closed late plate changed more than its own raw dump")
                erases += 1
    return {"rows": len(mobile.SETTINGS), "launches": len(trials), "pinned_erases": erases}


def coherent_triangle():
    """Exact Q(sqrt(-7)): t = exp(i gamma)/sqrt(2) = (1+sqrt(-7))/4.

    On each ordered pair apply t*[[1,1],[1,-1]], leave its spectator
    unchanged. Coordinates below are coefficients of 1 and sqrt(-7).
    """
    def scaled(x, y):
        return (x-7*y)/4, (x+y)/4

    rows = []
    for source in range(3):
        v = [(Fraction(i == source), Fraction(0)) for i in range(3)]
        for a, b in TRIANGLE:
            (x, y), (z, w) = v[a], v[b]
            v[a], v[b] = scaled(x+z, y+w), scaled(x-z, y-w)
        rows.append(tuple(x*x + 7*y*y for x, y in v))
    return tuple(rows)


def sole_overlap(rows):
    """A single shared support site makes row orthogonality impossible."""
    found = []
    for a, b in combinations(range(len(rows)), 2):
        shared = [c for c, (x, y) in enumerate(zip(rows[a], rows[b], strict=True)) if x*y]
        if len(shared) == 1:
            found.append((a, b, shared[0]))
    return tuple(found)


def switch_multiplicities(edges):
    return Counter(tuple(bits[a] ^ bits[b] for a, b in edges)
                   for bits in product((0, 1), repeat=3))


def verify():
    audit = audit_devices()
    two = two_arm()
    check(tuple(two.values()) == (32, 512, 256), "two-arm coverage")
    baseline = counts("S", CHAIN)
    first = counts("F", CHAIN)
    chain = counts("U", CHAIN)
    triangle = counts("U", TRIANGLE)
    repeated = counts("U", REPEATED)
    check(baseline == ((4, 3, 1), (4, 3, 1), (0, 2, 6)), "literal serial control")
    check(first == ((4, 3, 1), (4, 3, 1), (0, 4, 4)), "D correction control")
    check(chain == tuple(tuple(2*x for x in row) for row in fresh_counts(CHAIN))
          == ((4, 2, 2), (4, 2, 2), (0, 4, 4)), "unique path tree comparator")
    tree = switch_multiplicities(CHAIN)
    multiplicities = tuple(tree[b] for b in product((0, 1), repeat=2))
    check(multiplicities == (2, 2, 2, 2), "tree edge independence")
    cycle = switch_multiplicities(TRIANGLE)
    check(len(cycle) == 4 and all(sum(k) % 2 == 0 and v == 2 for k, v in cycle.items()),
          "cycle XOR constraint")
    check(triangle == ((2, 2, 4), (4, 2, 2), (2, 4, 2)), "cycle row")
    fresh = fresh_counts(TRIANGLE)
    check(fresh == ((3, 2, 3), (3, 2, 3), (2, 4, 2)), "fresh cycle control")
    coherent = coherent_triangle()
    check(coherent == tuple(tuple(Fraction(x, 8) for x in row) for row in triangle),
          "single repeated coherent coupler on triangle")
    check(repeated == ((6, 0, 2), (0, 6, 2), (2, 2, 4))
          and sole_overlap(repeated) == ((0, 1, 2),), "repeated-pair support wall")
    return {
        "scope": "finite scheduled classical fixture; one fixed complete three-mode unitary comparator only; no general QM exclusion or derivation",
        "device": audit, "two_arm": two,
        "vacuum_stationarity": "S flips only D on each vacant rail. Its iid pair law is fixed iff its one-arm marginal is flip-invariant (marginalize one arm; converse by product). Thus q(1,e)=q(2,e) for each e: fair D independent of E.",
        "stationary_crossing": {"kernel_over_two_D": crossing_kernel(),
            "formula": "source D replaced by 3 with the same E stock; for p=Pr(E=1), crossing=(2+1)*p*(1-p)/2 <= 3/8. Distinct source/vacuum stocks are not covered."},
        "chain_S_over_8": baseline, "chain_F_over_8": first, "chain_U_over_8": chain,
        "forest_chain_multiplicities": multiplicities,
        "forest_argument": "Given one root bit per component and XORs on distinct forest edges, recover every vertex bit along its unique tree path. The bijection sends fair iid bits to independent fair edge switches; repeated edges reuse their switch. Cycle XOR is zero.",
        "triangle_U_over_8": triangle, "triangle_fresh_over_8": fresh,
        "triangle_coherent": [[str(x) for x in row] for row in coherent],
        "coherent_fixture": "AB,BC,CA ordered; same e^(i gamma) H on each pair; spectator unchanged; cos(gamma)=1/(2 sqrt(2)). Comparator supplied, not inferred.",
        "repeated_U_over_8": repeated, "sole_support_overlap": sole_overlap(repeated),
        "wall": "Orthogonal pure launches A and B overlap only at output C; the single nonzero inner-product term cannot cancel, regardless of phases. Assumes one complete mode per detector and a fixed unitary. Hidden modes, channels and mixtures are not excluded.",
        "balanced_AB_BC_AB_bound": "Balanced two-mode couplers with spectator unchanged: A->B path magnitudes 1/2 and 1/(2 sqrt(2)); reverse triangle inequality gives P >= (3-2 sqrt(2))/8 > 0.",
        "stock": "Prepared hubs use fixed zero leaves and restored scratch 1 on each arm. One source D=3, other D=1, iid fair E. New two-arm plate B(0,E), closed raw D/E dumps with refill D=1 and fresh fair E. No between-hub resets in three-port runs."}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--json", action="store_true")
    args = parser.parse_args()
    report = verify()
    print(json.dumps(report, indent=2) if args.json else
          f"AB,BC,AB native counts /8: {report['repeated_U_over_8']}. {report['wall']}")


if __name__ == "__main__":
    main()
