"""Five depth settings exclude one fixed stochastic model with <=3 states.

Supplied comparison: rational equal-contact gates, coherent path controls,
one normalized preparation per requested word and square-norm counting of
all internal positions at a selected exit (no postselection). Depth n is
the requested number of H=012, G=123 contact pairs, not a shot counter.
The external readout, amplitude normalization and path coherence are
premises, not consequences of mobile ternary motion.

A four-path S4 splits into weights (-,+,+,+)/2. Two opposite-weight
paths carry the same fixed real reference y; the other two carry T^n e0
for T=S_G S_H. The same S4 recombination sends (T^n e0+y)/2 to exit
zero, so p_n=(1+<T^n e0,y>)/2. No continuous phase knob is used.

For any row-stochastic P with at most three states, pad by unused states.
Differences of one fixed prediction q_n=mu P^n r obey Delta[n+2] =
a*Delta[n+1]+b*Delta[n], a=tr(P)-1>=-1, b=-det(P). Because the other
two eigenvalues are in the unit disk, b>=-1 and b<=1-|a|. The coefficient
polygon has vertices (-1,-1),(-1,0),(0,1),(2,-1).

For the target differences let a*=-14/9 and D=d0*d2-d1^2. A two-row
elimination gives (a-a*)D while cancelling b; the row coefficient
norm divided by a-a* is at most (18/5)(|d0|+|d1|), checked at the four
vertices by convexity. Thus a common sup error is at least
(5/18)|D|/(|d0|+|d1|). This is a finite trace-sign obstruction,
not the repository's general asymptotic/peripheral spectrum argument.
"""

from __future__ import annotations

import json
from fractions import Fraction as F
from itertools import product

H = (0, 1, 2)
G = (1, 2, 3)
FIXED_TRACE = F(-14, 9)
VERTICES = ((-1, -1), (-1, 0), (0, 1), (2, -1))


def need(test, message):
    if not test:
        raise ArithmeticError(message)


def unit(i, n=4):
    return tuple(F(j == i) for j in range(n))


def dot(a, b):
    return sum(x * y for x, y in zip(a, b, strict=True))


def scatter(vector, ports):
    c = F(2 * sum(vector[p] for p in ports), len(ports))
    return tuple(c - a if i in ports else a for i, a in enumerate(vector))


def advance(vector):
    return scatter(scatter(vector, H), G)


def path_star(v):
    # Four separate S4 contacts, one at each internal position.
    return tuple(
        x
        for col in zip(*(scatter(v[j::4], range(4)) for j in range(4)), strict=True)
        for x in col
    )


def local_star(v, path, slots):
    return scatter(v, tuple(4 * path + k for k in slots))


def reference_setup(centered):
    v = path_star(unit(0, 16))
    for path in (0, 1):
        if centered:
            v = local_star(v, path, (0, 1))
            v = local_star(v, path, range(4))
        else:
            v = local_star(v, path, (0, 3))
    if centered:
        # The two reference arms have opposite amplitudes. Exchanging
        # their slot-2 values is a reciprocal S2, not a supplied minus gate.
        v = scatter(v, (2, 6))
        ref = (F(1, 2), F(-1, 2), F(-1, 2), F(1, 2))
    else:
        ref = unit(3)
    need(
        v[:4] == tuple(-x / 2 for x in ref) and v[4:8] == tuple(x / 2 for x in ref),
        "reference preparation failed",
    )
    need(dot(v, v) == dot(ref, ref) == 1, "reference circuit changed norm")
    return v, ref


def interferometer(horizon, centered=False):
    v, ref = reference_setup(centered)
    x = unit(0)
    result = []
    for _ in range(horizon + 1):
        measured = path_star(v)
        exit0 = measured[:4]
        need(
            exit0 == tuple((a + b) / 2 for a, b in zip(x, ref, strict=True))
            and dot(measured, measured) == 1,
            "direct real gate readout and cross-term formula disagree",
        )
        p = dot(exit0, exit0)
        need(p == (1 + dot(x, ref)) / 2 and 0 <= p <= 1, "binary exit marginal")
        result.append(p)
        for path in (2, 3):
            v = local_star(local_star(v, path, H), path, G)
        x = advance(x)
    return tuple(result)


def minus(a, b):
    return tuple(x - y for x, y in zip(a, b, strict=True))


def linear_identity():
    for i in range(4):
        seed = unit(i)
        first = minus(advance(seed), seed)
        second = advance(first)
        third = advance(second)
        need(
            third
            == tuple(FIXED_TRACE * y - x for x, y in zip(first, second, strict=True)),
            "(T²−a*T+I)(T−I)=0 matrix basis replay",
        )


def differences(seq):
    return tuple(seq[i + 1] - seq[i] for i in range(len(seq) - 1))


def residual_rows(a, b):
    r = (b, a - b, -1 - a, 1)
    return (*r, 0), (0, *r)


def certificate(seq):
    d0, d1, d2, d3 = differences(seq)
    need(
        d2 == FIXED_TRACE * d1 - d0 and d3 == FIXED_TRACE * d2 - d1,
        "target differences do not obey fixed quadratic",
    )
    determinant = d0 * d2 - d1 * d1
    need(determinant < 0, "degenerate planned trace")
    maxima = []
    for a, b in VERTICES:
        first, second = residual_rows(a, b)
        w = tuple(d1 * x - d0 * y for x, y in zip(first, second, strict=True))
        need(
            dot(w, seq) == (a - FIXED_TRACE) * determinant,
            "incorrect nuisance-term elimination",
        )
        maxima.append(F(sum(map(abs, w)), a - FIXED_TRACE))
    need(
        max(maxima) == F(18, 5) * (abs(d0) + abs(d1)), "exact coefficient norm control"
    )
    return F(abs(determinant), max(maxima)), determinant


def det3(p):
    x, y, z = p
    return sum(
        x[i] * (y[(i + 1) % 3] * z[(i + 2) % 3] - y[(i + 2) % 3] * z[(i + 1) % 3])
        for i in range(3)
    )


def predict(p, mu, response, horizon, *, signed=False):
    n = len(mu)
    need(
        len(p) == len(response) == n
        and sum(mu) == 1
        and min(mu) >= 0
        and all(0 <= t <= 1 for t in response),
        "fixed preparation/readout",
    )
    need(
        all(len(row) == n and sum(row) == 1 and (signed or min(row) >= 0) for row in p),
        "row stochastic",
    )
    state = mu
    out = []
    for _ in range(horizon + 1):
        out.append(dot(state, response))
        state = tuple(dot(state, col) for col in zip(*p, strict=True))
    return tuple(out)


def controls(seq, bound):
    anchors = (
        ((0, 1, 0), (0, 0, 1), (1, 0, 0)),  # 3-cycle
        ((0, 1, 0), (1, 0, 0), (1, 0, 0)),  # swap + feeding state
        ((0, 1, 0), (1, 0, 0), (0, 0, 1)),  # swap + fixed state
        ((1, 0, 0), (0, 1, 0), (0, 0, 1)),
    )
    need(
        tuple((sum(p[i][i] for i in range(3)) - 1, -det3(p)) for p in anchors)
        == VERTICES,
        "polygon vertices not independently realized",
    )
    rows = tuple(
        (F(i, 4), F(j, 4), F(4 - i - j, 4)) for i in range(5) for j in range(5 - i)
    )
    smallest = F(1)
    count = 0
    for p in product(rows, repeat=3):
        a, b = sum(p[i][i] for i in range(3)) - 1, -det3(p)
        need(a >= -1 and -1 <= b <= 1 - abs(a), "stochastic characteristic polygon")
        q = predict(p, (F(1, 3), F(1, 3), F(1, 3)), (0, F(1, 3), 1), 4)
        d = differences(q)
        need(
            d[2] == a * d[1] + b * d[0] and d[3] == a * d[2] + b * d[1],
            "independent stochastic recurrence replay",
        )
        gap = max(map(abs, minus(q, seq[:5])))
        need(gap >= bound, "finite stochastic model violated certified sup bound")
        smallest = min(smallest, gap)
        count += 1
    # For the ordinary reference, the first four readings DO admit a
    # three-state homogeneous model. The fifth is essential for this
    # contiguous prefix (not a claim about arbitrary queried depths).
    three_mix = F(seq[3] - seq[0], seq[1] - seq[0])
    three = (unit(1, 3), unit(2, 3), (1 - three_mix, three_mix, 0))
    need(
        predict(three, unit(0, 3), seq[:3], 3) == seq[:4],
        "five depth minimality for this contiguous prefix",
    )
    need(
        predict(three, unit(0, 3), seq[:3], 4) != seq[:5],
        "three-state control unexpectedly fit the fifth depth",
    )
    # Four homogeneous states already fit this particular five-point
    # prefix exactly: after visiting 0..3, yield p4 by mixing states 0/1.
    mix = F(seq[4] - seq[0], seq[1] - seq[0])
    four = (unit(1), unit(2), unit(3), (1 - mix, mix, 0, 0))
    need(
        predict(four, unit(0), seq[:4], 4) == seq[:5],
        "not an exact minimal-four-state prefix escape",
    )
    need(
        predict(four, unit(0), seq[:4], 5) != seq[:6],
        "four-state prefix control did not visibly stop fitting",
    )
    clock = tuple(unit(min(i + 1, 4), 5) for i in range(5))
    need(
        predict(clock, unit(0, 5), seq[:5], 4) == seq[:5],
        "five-state absorbing clock escape",
    )
    signed = ((0, 1, 0), (0, 0, 1), (1, F(5, 9), F(-5, 9)))
    need(
        predict(signed, unit(0, 3), seq[:3], len(seq) - 1, signed=True) == seq,
        "signed companion escape",
    )
    # Fixed binary response, but next-depth external programming changes
    # the transition. This is not a two-state homogeneous model.
    for n in range(len(seq) - 1):
        reset = ((1 - seq[n + 1], seq[n + 1]),) * 2
        need(
            predict(reset, (1 - seq[n], seq[n]), (0, 1), 1) == seq[n : n + 2],
            "programmable two-state reset",
        )
    return {
        "exact_three_state_grid_control_cases": count,
        "smallest_grid_error_for_this_one_fixed_preparation_and_response_not_an_optimum": str(
            smallest
        ),
        "three_state_exact_first_four_depths_last_row": tuple(map(str, three[-1])),
        "four_state_exact_five_depth_escape_last_row": tuple(map(str, four[-1])),
        "five_state_absorbing_clock_exact_prefix": True,
        "signed_three_state_exact_trace_last_row": tuple(map(str, signed[-1])),
        "programmable_two_state_exact_if_depth_dependent_transition_allowed": True,
    }


def five_depth_row(full, start, expected_bound, expected_margin):
    window = full[start : start + 5]
    bound, minor = certificate(window)
    margin = min(min(window), 1 - max(window))
    need(
        len(window) == 5
        and bound == expected_bound
        and margin == expected_margin
        and margin > 0,
        "predeclared exact separation or endpoint reserve changed",
    )
    return {
        "depths": tuple(range(start, start + 5)),
        "probability_exit_zero": tuple(map(str, window)),
        "target_difference_minor": str(minor),
        "minimum_common_sup_model_error_certified": str(bound),
        "smallest_probability_distance_from_zero_or_one": str(margin),
    }


def probe():
    linear_identity()
    standard = interferometer(7)
    alternate = interferometer(4, centered=True)
    need(
        standard[:2] == (F(1, 2), F(17, 18)) and alternate[0] == F(3, 4),
        "binary reference margin control",
    )
    d = differences(standard)
    need(
        all(d[j + 2] == FIXED_TRACE * d[j + 1] - d[j] for j in range(len(d) - 2)),
        "independent full trace recurrence",
    )
    # For a norm readout with the arm-cross term removed, each half-arm
    # contributes its squared norm 1/4; this is a control, not part of the
    # measured/prepared score or a mixture over depths.
    standard_read = five_depth_row(standard, 0, F(10, 207), F(1, 18))
    displaced_read = five_depth_row(standard, 3, F(162, 1387), F(17161, 1062882))
    balanced_ref = five_depth_row(alternate, 0, F(40, 297), F(209, 2916))
    return {
        "scope": "fixed complete classical state, one homogeneous nonnegative row-stochastic transition per H,G pair, fixed initial probability and fixed binary response; no experiment or all-finite-state claim",
        "unit_reference_predeclared": standard_read,
        "unit_reference_predeclared_offset_window": displaced_read,
        "centered_rational_reference_predeclared_alternative": balanced_ref,
        "uncombined_arm_squared_marginal_control": "1/2 at every depth if the cross term is absent; not used in any separating score",
        "hostile_and_escaping_controls": controls(standard, F(10, 207)),
        "operational_boundary": [
            "Ternary contacts supply real rational amplitudes only conditionally; the S4 splitter and recombiner also require the calibrated dyadic half-amplitude. Group all internal positions of the chosen exit as one event and count all prepared trials.",
            "The two request windows and two reference choices are separate defined comparisons; no pooling or switching the transition or readout within one trace. An offset is allowed for the lower bound because mu P^offset is itself a probability row.",
            "A bound excludes errors strictly below it. It is deterministic: inferred empirical probabilities would need simultaneous statistical intervals and independently bounded preparation/readout/gate errors.",
            "Three states means the complete internal simulator memory: hidden clocks, larger state spaces, depth-sensitive preparations or measurements, and signed weights are separate alternative models.",
        ],
    }


if __name__ == "__main__":
    print(json.dumps(probe(), sort_keys=True, separators=(",", ":")))
