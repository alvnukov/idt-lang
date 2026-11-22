"""Independent finite audit of a signed walk on a rooted folded-five graph.

Graph polynomials are standard signal filters (Sandryhaila and Moura,
arXiv:1210.4752). Here the finite identities are checked exactly, without
using a graph-filter uniqueness theorem, numerical eigensolver, or another
probe. The spectrum, absorber, parity flag, ordered preparation, choice
of walk rule and any normalization are not inferred from physical data.

Writing L+=(3+sqrt(41))/2 and L-=(3-sqrt(41))/2, the deleted adjacency
has eigenvalues L+, L-, 1 and -3. For nonnegative wait weight w, the
most amplified magnitude of wI-A_D is w+3 precisely when w is above
(sqrt(41)-3)/4. Equality ties w+3 with the negative Perron image; below
the threshold the latter wins. In the successful regime, the unwanted
to target spectral-radius ratio is minimized at w=3/2: below that the
numerator L+-w decreases, above it w-L- increases relative to w+3.
This optimizes a normalized linear filter, not survival or sample cost.

A stochastic implementation counts the parity of genuine hops and
keeps absorbed attempts. Its raw contrast *decays*, even in the above
regime, and summing over endpoints or into the one root detector erases
the four-dimensional desired mode. Keeping the incoming port provides
a local first-absorption readout of only the five port values, without
a remote endpoint lookup. A norm-preserving unitary is not this absorbing,
branching or normalized spectral iteration.
"""

from __future__ import annotations

import json
from decimal import Decimal, localcontext
from fractions import Fraction

N = 16
Matrix = tuple[tuple[int, ...], ...]
Vector = tuple[int, ...]
PORTS = (1, 2, 4, 8, 16)


def need(condition, why):
    if not condition:
        raise ArithmeticError(why)


def fixture() -> dict[int, frozenset[int]]:
    def fold(x):
        return min(x, x ^ 31)

    return {v: frozenset(fold(v ^ bit) for bit in PORTS) for v in range(N)}


def adjacency(graph, vertices: tuple[int, ...]) -> Matrix:
    return tuple(tuple(int(v in graph[u]) for v in vertices) for u in vertices)


def ident(n: int) -> Matrix:
    return tuple(tuple(int(i == j) for j in range(n)) for i in range(n))


def linear(*terms: tuple[int, Matrix]) -> Matrix:
    n = len(terms[0][1])
    return tuple(tuple(sum(c*m[i][j] for c, m in terms) for j in range(n)) for i in range(n))


def mm(left: Matrix, right: Matrix) -> Matrix:
    cols = tuple(zip(*right, strict=True))
    return tuple(tuple(sum(a*b for a, b in zip(row, col, strict=True)) for col in cols) for row in left)


def mv(matrix: Matrix, vector: Vector) -> Vector:
    return tuple(sum(a*b for a, b in zip(row, vector, strict=True)) for row in matrix)


def diagonal_sum(matrix: Matrix) -> int:
    return sum(row[i] for i, row in enumerate(matrix))


def column(matrix: Matrix, j: int) -> Vector:
    return tuple(row[j] for row in matrix)


def unit(size: int, index: int) -> Vector:
    return tuple(int(i == index) for i in range(size))


def spectrum_pinned(graph, r: int, vertices: tuple[int, ...], full: Matrix) -> tuple[Matrix, Matrix]:
    a = adjacency(graph, vertices)
    i = ident(len(a))
    a2, a3 = mm(a, a), mm(mm(a, a), a)
    quadr = linear((1, a2), (-3, a), (-8, i))
    need(mm(mm(linear((1, a), (-1, i)), linear((1, a), (3, i))), quadr) == linear((0, i)),
         "pinned matrix does not obey the stated annihilating polynomial")
    # Orthogonal projectors scaled by 40 to retain exact integer matrices.
    negative = linear((-1, a3), (4, a2), (5, a), (-8, i))
    positive_one = linear((-1, a3), (17, a), (24, i))
    for projected, eigenvalue, dim in ((negative, -3, 4), (positive_one, 1, 9)):
        need(mm(projected, projected) == linear((40, projected))
             and mm(a, projected) == linear((eigenvalue, projected))
             and diagonal_sum(projected) == 40*dim, "spectral projector check")
    # The remaining two dimensions are spanned by the root-shell constants.
    for v in vertices:
        count = tuple(len(graph[v] & side) for side in (graph[r], frozenset(vertices) - graph[r]))
        need(count == ((0, 4) if v in graph[r] else (2, 3)), "root-shell quotient is not equitable")
    need(all(2*negative[i][j] == 5*full[u][v]-full[u][r]*full[r][v]
             for i, u in enumerate(vertices) for j, v in enumerate(vertices)), "pin is not orthogonal compression")
    return a, negative


def full_projector(graph) -> Matrix:
    a = adjacency(graph, tuple(range(N)))
    i = ident(N)
    j = tuple((1,) * N for _ in a)
    need(mm(a, a) == linear((3, i), (-2, a), (2, j)), "not the strongly regular folded-five relation")
    f = linear((4, i), (-4, a), (1, j))
    need(mm(f, f) == linear((16, f)) and mm(a, f) == linear((-3, f)) and diagonal_sum(f) == 80,
         "full graph projector or multiplicity changed")
    # Full graph spectrum follows from symmetry, the displayed quadratic
    # relation on the mean-zero space and the degree-five constant mode.
    need(all(sum(row) == 0 for row in f) and all(sum(row) == 5 for row in a), "full mean modes changed")
    return f


def occupation(graph, r: int, t: int) -> Vector:
    """Independent expected readout after selecting the two (or one) root ports."""
    ports = graph[r]
    block_b = {t} if t in ports else ports & graph[t]
    a, b = -len(block_b), len(ports)-len(block_b)
    weights = {u: b if u in block_b else a for u in ports}
    return tuple(0 if v == r else -weights[v] if v in ports
                 else sum(weights[u] for u in ports & graph[v]) for v in range(N))


def first_order_charge(graph, r: int, t: int) -> Vector:
    need(t != r and t not in graph[r], "formula needs distinct nonadjacent ordered markers")
    return tuple(1+5*int(v == t)-5*int(v in graph[t])-int(v == r)+int(v in graph[r]) for v in range(N))


def audit_mark_sources(graph, r: int, t: int, vertices: tuple[int, ...], a: Matrix,
                       projected: Matrix, full: Matrix) -> dict[str, object]:
    for j, mark in enumerate(vertices):
        expected = occupation(graph, r, mark)
        sign = -1 if mark in graph[r] else 1
        need(column(projected, j) == tuple(2*sign*expected[v] for v in vertices),
             "prepared source did not reproduce the independent occupation comparator")
        if mark not in graph[r]:
            need(first_order_charge(graph, r, mark) == expected, "one-hop contrast and charge differ")
    # Every centered weight vector maps to a -3 field; these four tested
    # independent vectors already account for the entire pinned mode.
    root_ports = tuple(sorted(graph[r]))
    basis = []
    for i in range(4):
        weights = {u: int(u == root_ports[i])-int(u == root_ports[-1]) for u in root_ports}
        col = tuple(-weights[v] if v in weights else sum(weights[u] for u in graph[v] & graph[r])
                    for v in vertices)
        need(mv(a, col) == tuple(-3*v for v in col), "centered occupation candidate is not an eigenfield")
        basis.append(col)
    need(tuple(tuple(col[vertices.index(u)] for u in root_ports[:-1]) for col in basis)
         == linear((-1, ident(4))), "field candidates not independent")
    sums = {"root_neighbors": tuple(sum(row[j] for j, v in enumerate(vertices) if v in graph[r])
                                    for row in projected),
            "root_nonneighbors": tuple(sum(row[j] for j, v in enumerate(vertices) if v not in graph[r])
                                       for row in projected)}
    need(all(not any(col) for col in sums.values()), "unresolved shell-uniform mark did not average away")
    need(all(sum(row) == 0 for row in projected), "whole-endpoint aggregation not orthogonal to charge")
    need(all(sum(projected[i][j] for i, v in enumerate(vertices) if v in graph[r]) == 0
             for j in range(len(vertices))), "root detector sees pinned charge mode")
    raw_pair = tuple(row[t]-row[r] for row in full)
    need(raw_pair[r] == -4, "unweighted difference accidentally pinned the vacuum")
    q = first_order_charge(graph, r, t)
    need(tuple(5*row[t]-row[r] for row in full) == tuple(4*x for x in q),
         "root-retaining compensated filter changed")
    return {"pinned_mode_dimension": 4, "unpinned_mode_dimension": 5,
            "unpinning_wait_one": "adjacency 5 and -3 give tied -4 and +4 iteration magnitudes",
            "unpinning_wait_above_one": "5D centered eigenspace dominates but does not pin the vacuum",
            "root_site_and_sum_over_root_ports_vanish": True,
            "uniform_mark_in_either_shell": "zero projection",
            "adjacent_mark": "4+1 occupation field, with opposite sign for same positive-mark convention",
            "unweighted_root_free_pair_difference": "not pinned, root entry of P(e_t-e_r) is -1/4",
            "unpinned_compensated_source": "P(5*delta_t-delta_r)=q/4; contrasted ordered source supplied"}


def spectral_regimes() -> dict[str, object]:
    # For w>=0, (4w+3)^2 > 41 iff w > w*, without floating threshold decisions.
    samples = (Fraction(0), Fraction(1, 2), Fraction(17, 20), Fraction(43, 50),
               Fraction(1), Fraction(3, 2), Fraction(2))
    regimes = ["charge" if (4*w+3)**2 > 41 else "negative_perron" for w in samples]
    need(regimes == ["negative_perron"]*3 + ["charge"]*4, "wait threshold samples")
    with localcontext() as ctx:
        ctx.prec = 36
        sqrt41 = Decimal(41).sqrt()
        lam_plus, lam_minus = (3+sqrt41)/2, (3-sqrt41)/2

        def dec(x):
            return Decimal(x.numerator) / Decimal(x.denominator)

        def rate(w):
            return max(abs(w-lam_plus), abs(w-lam_minus), abs(w-1)) / (w+3)

        need(rate(Decimal("1.5")) < rate(Decimal(1)) and rate(Decimal("1.5")) < rate(Decimal(2)),
             "interior optimal wait control")
        return {"lambda_plus_decimal": format(lam_plus, ".9f"),
                "equality": "tied +/- leading magnitudes; a point source has a nonzero Perron component",
                "threshold": "(sqrt(41)-3)/4", "threshold_decimal": format((sqrt41-3)/4, ".9f"),
                "sample_modes_by_wait": {str(w): mode for w, mode in zip(samples, regimes, strict=True)},
                "optimal_wait_for_normalized_spectral_separation": "3/2",
                "optimal_subleading_ratio": "sqrt(41)/9",
                "sample_subleading_ratios_in_charge_regime_decimal": {
                    str(w): format(rate(dec(w)), ".9f") for w in samples if (4*w+3)**2 > 41
                },
                "wait_one_survival_factor_decimal": format((1+lam_plus)/6, ".9f"),
                "wait_one_raw_contrast_factor": "2/3",
                "wait_one_conditional_ratio_factor_decimal": format(4/(1+lam_plus), ".9f")}


def parity_attempts(a: Matrix, start: int, wait: int, hop: int, steps: int
                    ) -> list[tuple[Vector, Vector, int]]:
    even, odd = unit(len(a), start), (0,) * len(a)
    signed = even
    outcomes = [(even, odd, 1)]
    kernel = linear((wait, ident(len(a))), (-hop, a))
    for n in range(1, steps+1):
        into_even, into_odd = mv(a, odd), mv(a, even)
        even = tuple(wait*x + hop*y for x, y in zip(even, into_even, strict=True))
        odd = tuple(wait*x + hop*y for x, y in zip(odd, into_odd, strict=True))
        signed = mv(kernel, signed)
        total = (wait+5*hop)**n  # attempted choices, including absorbed histories
        need(tuple(x-y for x, y in zip(even, odd, strict=True)) == signed
             and sum(even)+sum(odd) <= total, "parity and all-attempt count mismatch")
        outcomes.append((even, odd, total))
    return outcomes


def walk_audit(graph, r: int, t: int, vertices: tuple[int, ...], a: Matrix,
               q: Vector) -> tuple[dict[str, object], list[tuple[Vector, Vector, int]]]:
    projected = tuple(q[v] for v in vertices)
    report = {}
    attempts = []
    for wait, hop, reliable_bound in ((1, 1, Fraction(15, 16)), (3, 2, Fraction(3, 4))):
        outcomes = parity_attempts(a, vertices.index(t), wait, hop, 48)
        exact_errors = {}
        for step in (4, 12, 24, 48):
            even, odd, attempts_total = outcomes[step]
            diff = tuple(x-y for x, y in zip(even, odd, strict=True))
            scale = (wait+3*hop)**step
            err2 = sum((Fraction(s, scale)-Fraction(value, 20))**2
                       for s, value in zip(diff, projected, strict=True))
            need(err2 <= reliable_bound**(2*step), "exact convergence bound")
            exact_errors[str(step)] = {
                "normalized_error_squared_decimal": f"{float(err2):.4g}",
                "live_probability_decimal": f"{(sum(even)+sum(odd))/attempts_total:.5g}",
                "maximum_absolute_parity_bias_given_live_endpoint_decimal":
                    f"{max(abs(Fraction(s, e+o)) for s, e, o in zip(diff, even, odd, strict=True) if e+o):.5g}",
            }
        first_joint_support = next(i for i, (e, o, _) in enumerate(outcomes) if min(e) > 0 and min(o) > 0)
        first_odd_actual_return = next(i for i, (_, o, _) in enumerate(outcomes) if o[vertices.index(t)] > 0)
        need(first_odd_actual_return == 5, "odd actual return of killed graph changed")
        report[str(Fraction(wait, hop))] = {
            "first_time_both_parities_reach_every_live_endpoint": first_joint_support,
            "first_odd_actual_return": first_odd_actual_return,
            "sampled_errors_and_detection_rates": exact_errors,
        }
        if wait == hop == 1:
            attempts = outcomes
    no_wait = parity_attempts(a, vertices.index(t), 0, 1, 10)
    need(all(not any(e if n % 2 else o) for n, (e, o, _) in enumerate(no_wait)),
         "no wait changed the fixed parity of every surviving path")
    need(sum(q[v] for v in graph[r]) == 0 and sum(q) == 0, "charge is visible in root flux or total survival")
    return {"weighted_live_walks": report,
            "no_wait": "same sign on all paths at any fixed time; unsigned shape",
            "unsigned": "positive Perron shape on both root shells; not the centered sector",
            "aggregated_root_detector": "signed flux into root and total survival parity both annihilate charge mode",
            "port_resolved_root_detector": "signed first-arrival flux at n+1 is -S_n(u) per incoming u"}, attempts


def finite_binary_readouts(graph, r: int, t: int, vertices: tuple[int, ...], q: Vector,
                          attempts: list[tuple[Vector, Vector, int]]) -> dict[str, object]:
    # 40P = T^3 + T^2 - 10T for T=I-A_D. Pick lengths 3,2,1 with
    # weights 216,36,60. Marked endpoint: report parity (inverted at
    # length 1); other or absorbed endpoint: report a fair bit.
    weights = ((3, 216, 1), (2, 36, 1), (1, 60, -1))
    total = sum(w for _, w, _ in weights)
    parity_probabilities = []
    for j, v in enumerate(vertices):
        count_probability = Fraction(1, 2)
        for n, weight, direction in weights:
            even, odd, attempted = attempts[n]
            count_probability += Fraction(weight * direction * (even[j]-odd[j]), 2*total*attempted)
        need(count_probability == Fraction(1, 2)+Fraction(q[v], total),
             "finite predeclared raw parity event failed")
        parity_probabilities.append(str(count_probability))

    root_probabilities = {}
    root_ports = tuple(sorted(graph[r]))
    for u in root_ports:
        j = vertices.index(u)
        count_probability = Fraction(1, 2)
        for n, weight, direction in weights:
            even, odd, attempted = attempts[n]
            # Exactly one root port among the six equal choices. A root
            # hit at this length is necessarily the first, since the
            # state distributions already removed previous hits.
            arrivals_even, arrivals_odd = odd[j], even[j]
            count_probability += Fraction(weight * direction * (arrivals_even-arrivals_odd), 2*total*6*attempted)
        need(count_probability == Fraction(1, 2)-Fraction(q[u], 6*total),
             "predeclared port-resolved first-arrival readout failed")
        root_probabilities[str(u)] = str(count_probability)
    need(sum(map(Fraction, root_probabilities.values())) == Fraction(5, 2), "pooled port contrast did not cancel")

    # No killed walk, no parity, no negative count: each atom is one
    # of four specified experiments with a hit or miss event at v.
    trials = [(t, True)]*5 + [(u, False) for u in graph[t] for _ in range(5)]
    trials += [(r, False)] + [(u, True) for u in graph[r]]
    need(len(trials) == 36, "bad one-hop trial atom census")
    probabilities = [Fraction(sum((end == v) == decision for end, decision in trials), len(trials))
                     for v in graph]
    need(tuple(probabilities) == tuple(Fraction(q[v]+25, 36) for v in graph),
         "positive 0/1-hop event and centered charge differ")
    return {
        "predeclared_parity_filter": {"event_uses_signed_arithmetic": False,
                                     "uses_parity_flag_and_absorber": True,
                                     "offset_from_fair_baseline": "q(v)/312",
                                     "sample_probabilities": sorted(set(parity_probabilities))},
        "predeclared_port_resolved_first_absorption": {
            "endpoint_lookup_beyond_root": False,
            "supplied": ["incoming_port_record", "hop_parity_flag", "fixed_elapsed_trial_lengths", "fair_baseline"],
            "lengths": [2, 3, 4],
            "offset_from_fair_baseline": "-q(u)/1872",
            "probabilities_by_incoming_port": root_probabilities,
            "pooled_offset": 0,
        },
        "one_hop_mixture": {"uses_absorber": False, "uses_parity_flag": False,
                            "uses_ordered_markers": True, "supplied_trial_weights": [5, 25, 1, 5],
                            "event_probability": "(q(v)+25)/36",
                            "subtract_supplied_root_baseline_for_signed_quantity": "25/36",
                            "min_probability": str(min(probabilities)), "max_probability": str(max(probabilities))},
    }


def probe() -> dict[str, object]:
    graph, root = fixture(), 0
    live = tuple(v for v in graph if v != root)
    target = min(set(live) - graph[root])
    full = full_projector(graph)
    a, p = spectrum_pinned(graph, root, live, full)
    mark_audit = audit_mark_sources(graph, root, target, live, a, p, full)
    q = first_order_charge(graph, root, target)
    walk, attempts = walk_audit(graph, root, target, live, a, q)
    return {
        "scope": "finite graph filters and calibrated binary observations only; no physical inference",
        "pinned_spectrum": {"-3": 4, "1": 9, "(3-sqrt(41))/2": 1, "(3+sqrt(41))/2": 1},
        "pinned_projection_scale": "P_D delta_t=q/20 for a nonadjacent mark",
        "charge_multiplicity": {str(x): q.count(x) for x in sorted(set(q))},
        "source_controls": mark_audit, "spectral_regimes": spectral_regimes(),
        "live_counts": walk, "finite_readout_controls": finite_binary_readouts(graph, root, target, live, q, attempts),
        "physical_boundary": "branching and a nonlocal normalization do not show passive unitary mode selection,"
                             " nor are the marks, parity or readout calibration inferred",
    }


if __name__ == "__main__":
    print(json.dumps(probe(), sort_keys=True, separators=(",", ":")))
