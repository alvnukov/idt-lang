"""Four-entry interval and fixed-count tests of one fixed complete 3-mode U.

Run: python3 -m scripts.probe_three_port_dark_bounds [--json]
Rows are orthogonal source ports; columns are resolved detections. No empirical
sample, universal physics claim, or statistical model for the eight enumerated
shade triples. The count example is hypothetical and separate from enumeration.
"""

import argparse
from collections import Counter
from dataclasses import dataclass
from fractions import Fraction as F
from itertools import product
import json
from math import comb

from scripts import probe_vacuum_compensated_network as net
from scripts.probe_eight_label_interferometer import check


@dataclass(frozen=True)
class Scope:
    orthogonal_inputs: bool | None = None
    single_mode_per_port: bool | None = None
    complete_three_ports: bool | None = None
    all_launches_accounted: bool | None = None
    same_device_and_settings: bool | None = None


@dataclass(frozen=True)
class CountPlan:
    """Frozen before collecting data, with a fixed sample size for each row."""
    c: F
    z: F
    alpha: F
    n_a: int
    n_b: int
    preregistered: bool
    iid_within_each_row: bool


def _result(reason, excluded=False):
    return {"excluded": excluded, "status": "excludes_fixed_3mode_U" if excluded
            else "inconclusive", "reason": reason}


def _scoped(scope):
    return isinstance(scope, Scope) and all(value is True for value in vars(scope).values())


def _unit(value):
    # Accept only exact probabilities, never round a boundary or accept bool as int.
    return type(value) in (int, F) and 0 <= value <= 1


def interval_verdict(intervals, scope):
    """Necessary condition; non-exclusion is not a witness of a unitary.

    For lower bright bounds a,b and upper darks x,y, row orthogonality
    demands sqrt(a*b) <= sqrt((1-a-X)*Y) + sqrt(X*(1-b-Y)) for some
    actual X<=x,Y<=y. With X=(1-a)sin²u, Y=(1-b)sin²v the RHS equals
    sqrt((1-a)(1-b))*sin(u+v); it is maximal at x,y if u+v<=pi/2
    throughout, equivalently x/(1-a)+y/(1-b)<=1. Else use the global
    sin<=1 bound (already caught if violated by the column-sum check).

    In particular for a=b=c, X,Y<=z<=(1-c)/2, put t=1-c. Cauchy gives
    RHS² <= (2t-X-Y)(X+Y) <= 4z(t-z), without imposing X=Y.
    Sharp: d in [0,1/2], z=d²,c=2d(1-d). Rows (1-d,-d,sqrt(c)),
    (-d,1-d,sqrt(c)),(sqrt(c),sqrt(c),2d-1) are real orthonormal.
    At c=1/4 this forces max(X,Y)>=(3-2sqrt(2))/8, not BOTH darks.
    """
    if not _scoped(scope):
        return _result("scope unknown or violated (e.g. unresolved/censored outcomes)")
    if not isinstance(intervals, dict) or set(intervals) != {"AB", "BA", "AC", "BC"}:
        return _result("need simultaneous bounds on exactly AC, BC, AB, BA")
    for bounds in intervals.values():
        if (not isinstance(bounds, (list, tuple)) or len(bounds) != 2
                or not all(_unit(v) for v in bounds) or bounds[0] > bounds[1]):
            return _result("invalid exact probability interval")
    a, b = intervals["AC"][0], intervals["BC"][0]
    t, s = 1 - a, 1 - b
    if intervals["AB"][0] > t or intervals["BA"][0] > s:
        return _result("inconsistent probability bounds within an input row")
    if a + b > 1:
        return _result("third column norm exceeds one", True)
    x, y = min(intervals["AB"][1], t), min(intervals["BA"][1], s)
    if t * s == 0 or x * s + y * t > t * s:
        return _result("no exclusion by this upper bound")
    u, v = (t - x) * y, x * (s - y)
    # Compare sqrt(a*b) > sqrt(u)+sqrt(v) without floating point.
    gap = a * b - u - v
    if gap > 0 and gap * gap > 4 * u * v:
        return _result("two dark terms cannot cancel the common bright term", True)
    return _result("no exclusion by this upper bound")


def removal_witnesses():
    """Two squared rows of a real orthogonal completion for each omitted cell.

    The original four values are AC=BC=1/4 and AB=BA=0. Each pair of
    normalized rows has disjoint support or two equal overlap magnitudes:
    pick opposite signs at those coordinates, then take the cross product as
    the third row. Thus none of the four original entries is redundant.
    """
    return {"AC": ((1, 0, 0), (0, F(3, 4), F(1, 4))),
            "BC": ((F(3, 4), 0, F(1, 4)), (0, 1, 0)),
            "AB": ((F(2, 3), F(1, 12), F(1, 4)), (0, F(3, 4), F(1, 4))),
            "BA": ((F(3, 4), 0, F(1, 4)), (F(1, 12), F(2, 3), F(1, 4)))}


def _tail(n, p, indices):
    h, d = p.numerator, p.denominator
    return F(sum(comb(n, k) * h**k * (d-h)**(n-k) for k in indices), d**n)


def count_verdict(rows, scope, plan):
    """Four exact one-sided binomial tests with Bonferroni level alpha/4.

    Within an input row, each cell count is marginally binomial under the
    stated iid design. Cross-cell/row independence is not used in the union
    bound. Fixed thresholds and sample sizes, no peeking, optional stopping,
    multiple design searches or postselection. Threshold-tail probabilities
    are not posterior probabilities for a model or an event rate.
    """
    if not _scoped(scope):
        return _result("unverified mode/accounting/device scope")
    if (not isinstance(plan, CountPlan) or plan.preregistered is not True
            or plan.iid_within_each_row is not True
            or not all(_unit(v) for v in (plan.c, plan.z, plan.alpha))
            or not 0 < plan.alpha < 1
            or not all(type(n) is int and n > 0 for n in (plan.n_a, plan.n_b))):
        return _result("invalid/unknown fixed iid counting design")
    c, z = plan.c, plan.z
    if not interval_verdict({"AC": (c, 1), "BC": (c, 1),
                             "AB": (0, z), "BA": (0, z)}, scope)["excluded"]:
        return _result("predeclared thresholds do not violate the bound")
    if not isinstance(rows, (list, tuple)) or len(rows) != 2:
        return _result("need two raw fixed-size rows with all three counts")
    for row, n in zip(rows, (plan.n_a, plan.n_b), strict=True):
        if (not isinstance(row, (list, tuple)) or len(row) != 3
                or any(type(k) is not int or k < 0 for k in row) or sum(row) != n):
            return _result("invalid or incomplete raw row")
    tails = {}
    for row, n, bright, dark, j in zip(rows, (plan.n_a, plan.n_b), ("AC", "BC"),
                                       ("AB", "BA"), (1, 0), strict=True):
        tails[bright] = _tail(n, c, range(row[2], n+1))
        tails[dark] = _tail(n, z, range(row[j]+1))
    rejected = all(t <= F(plan.alpha) / 4 for t in tails.values())
    return {**_result("four preset tail tests passed" if rejected else
                      "finite counts insufficient for the preset certificate", rejected),
            "tails": tails}


def _physical_word():
    # One persistent D,E,Z,scratch quadruple per port, including between
    # the two copies. The parent's local word numbers its scratch cells 6,7.
    layers = []
    for a, b in net.REPEATED:
        slots = (4*a, 4*a+1, 4*a+2, 4*b, 4*b+1, 4*b+2, 4*a+3, 4*b+3)
        layers.extend(tuple((slots[i], slots[j]) for i, j in layer) for layer in net.WORDS["U"])
    return tuple(layers)


def _product(a, b):
    return tuple(tuple(sum(row[k]*b[k][j] for k in range(3)) for j in range(3)) for row in a)


def _raw_port(state):
    raw = [state[4*i:4*i+4].count(3) for i in range(3)]
    check(sum(raw) == 1 and all(state[4*i+2:4*i+4] == (0, 1) for i in range(3)),
          "uncounted token or unrestored auxiliary")
    return raw.index(1)


def echo_controls():
    """Three distinct two-block predictions sharing the same one-block T."""
    word = _physical_word()
    seeds = tuple(product(net.SHADES, repeat=3))
    singles, doubles, restored = [], [], 0
    launch_maps = {shades: [] for shades in seeds}
    for source in range(3):
        first, second = [0]*3, [0]*3
        for shades in seeds:
            raw = tuple(v for i, e in enumerate(shades) for v in (3 if i == source else 1, e, 0, 1))
            mid = net.mobile._replay(raw, word).output
            end = net.mobile._replay(mid, word).output  # same cells; no reset/readout action
            first[_raw_port(mid)] += 1
            second[_raw_port(end)] += 1
            launch_maps[shades].append(_raw_port(mid))
            restored += end == raw
        singles.append(tuple(first))
        doubles.append(tuple(second))
    one, twice = tuple(singles), tuple(doubles)
    check(one == net.counts("U", net.REPEATED) and restored == 24, "literal schedule echo")
    histogram = Counter(map(tuple, launch_maps.values()))
    check(histogram == {(0, 1, 2): 4, (2, 1, 0): 2, (0, 2, 1): 2}, "frozen permutation mixture")
    fresh = _product(one, one)  # independent new shade triple per whole ABA block
    perms = tuple(tuple(sum(count for perm, count in histogram.items() if perm[perm[i]] == j)
                        for j in range(3)) for i in range(3))

    # A fixed fair AC-or-BC choice, then a balanced coupler with intermediate
    # path dephasing: conditional probability kernel K=(I+swap)/2 has K²=K.
    dephased = [[0]*3 for _ in range(3)]
    coherent = [[0]*3 for _ in range(3)]
    h = ((1, 1), (1, -1))  # active 2x2 amplitude block is h/sqrt(2)
    for a, b in ((0, 2), (1, 2)):
        swap = list(range(3))
        swap[a], swap[b] = b, a
        k2 = tuple(tuple(int(i == j) + int(swap[i] == j) for j in range(3)) for i in range(3))
        square = _product(k2, k2)
        check(all(square[i][j] == 2*k2[i][j] for i, j in product(range(3), repeat=2)),
              "fixed balanced kernel must be idempotent")
        for i, j in product(range(3), repeat=2):
            dephased[i][j] += square[i][j]  # fair choice times denominator 4 -> /8
            if i in (a, b) and j in (a, b):
                u, v = (a, b).index(i), (a, b).index(j)
                coherent[i][j] += sum(h[u][k]*h[k][v] for k in range(2))**2
            else:
                coherent[i][j] += 4*int(i == j)  # uncoupled spectator
    fixed = tuple(map(tuple, dephased))
    coherent = tuple(map(tuple, coherent))
    check(fixed == one and coherent == perms == twice, "named comparator rows")
    return {"one_over_8": one, "shared_over_8": twice, "fresh_over_64": fresh,
            "fixed_dephased_over_8": fixed, "fixed_permutation_over_8": perms,
            "fixed_coherent_over_8": coherent,
            "raw_launches_restored": restored}


def verify():
    scope = Scope(True, True, True, True, True)
    echo = echo_controls()
    a, b = echo["one_over_8"][:2]
    exact = {key: (F(n, 8), F(n, 8)) for key, n in zip(
        ("AC", "BC", "AB", "BA"), (a[2], b[2], a[1], b[0]), strict=True)}
    census = interval_verdict(exact, scope)
    check(census["excluded"], "complete single-mode comparator against the literal one-block row")
    # Hypothetical counts, not 64 repetitions of an eight-state census.
    plan = CountPlan(F(1, 5), F(1, 100), F(1, 20), 512, 512, True, True)
    counts = count_verdict(((384, 0, 128), (0, 384, 128)), scope, plan)
    check(counts["excluded"], "hypothetical preset test")
    return {"scope": "finite scheduled classical fixture; only a fixed complete single-mode "
                     "3x3 U is tested. Mixtures, extra modes and channels remain possible.",
            "symmetric_threshold": "At c=1/4 at least one cross-dark probability must be "
                                   "at least (3-2sqrt(2))/8. Equality is attainable.",
            "literal_interval": census,
            "four_entry_minimality": "Each three-entry subset of AC=BC=1/4, AB=BA=0 "
                                     "has an explicit real orthogonal completion (removal_witnesses).",
            "hypothetical_fixed_count_example": {
                "raw_rows": ((384, 0, 128), (0, 384, 128)), "alpha": "1/20",
                "predeclared_c": "1/5", "predeclared_z": "1/100",
                "bonferroni_per_tail": "1/80", "excluded_under_stated_scope": counts["excluded"],
                "tail_probabilities_approx": {k: float(v) for k, v in counts["tails"].items()}},
            "echo": echo,
            "echo_boundary": "Shared shade and fixed-permutation models both return I. A fixed "
                             "fair AC-or-BC coherent balanced Hadamard also returns I (H²=I). "
                             "Dephasing that same fixed pair gives T; fresh independent ABA "
                             "block stock gives T². No model identification from the echo alone."}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--json", action="store_true")
    args = parser.parse_args()
    report = verify()
    print(json.dumps(report, indent=2) if args.json else
          f"{report['symmetric_threshold']} {report['echo_boundary']}")


if __name__ == "__main__":
    main()
