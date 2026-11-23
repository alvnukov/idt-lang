"""One-visit phase budget from endpoint distributions only.

Each trial has an exclusive path. The complete setting-independent
preparation, including correlated detector stock, fixes which of two
isolated toggles (if either) the path can hear. Only the occupied branch
may convey its local bit; no setting leaks through an empty arm, timing,
herald, or the detector. Its occupied-branch hidden response can be
arbitrary. We use normalized rows of ALL preparations, with loss an
outcome, and never estimate intermediate path frequencies.

Under this causal model p_xy = c + A_x + B_y with nonnegative row
measures of fixed masses, hence p00+p11=p01+p10 componentwise. The
converse follows by per-output minima: take c=min(p00,p01,p10,p11),
A_x=p_x0-min_u p_u0, B_y=p_0y-min_v p_0v. The resulting component
masses are independent of the toggles by normalization. Equivalently
sample a route and its two potential output tickets before the settings.

For parity rows (P,Q,Q,P), let r=TV(P,Q), including all outcomes. The
closest one-visit table has uniform per-row TV error r/2. A mixture
with one setting-independent fraction beta allowed arbitrary two-bit
response needs beta >= max(0,r-2*epsilon) at per-row error epsilon;
for three contexts 00,01,10 only the corresponding coefficient is
three, and both bounds are sharp. Neither the exclusion nor a fitted
mixture identifies what leaks in a real device. No Bell claim follows.

For the four-setting bound, the unscaled defect has TV norm 2r, a
normalized arbitrary table has defect norm <=2, and four perturbed
rows contribute <=4*epsilon. For three settings use the event contrast
p00(D)-p01(D)-p10(D), which is <=0 on one-visit tables and <=1 on
arbitrary tables; its three-row error is at most 3*epsilon.
"""

from __future__ import annotations

import json
from fractions import Fraction as F
from itertools import combinations_with_replacement, product

CONTEXTS = ((0, 0), (0, 1), (1, 0), (1, 1))
H = (0, 1, 2)
G = (1, 2, 3)


def need(test, message):
    if not test:
        raise ArithmeticError(message)


def add(*rows):
    return tuple(map(sum, zip(*rows, strict=True)))


def scale(row, factor):
    return tuple(factor * a for a in row)


def difference(a, b):
    return add(a, scale(b, -1))


def norm_tv(signed):
    return F(sum(map(abs, signed)), 2)


def tv(a, b):
    return norm_tv(difference(a, b))


def defect(rows):
    a, b, c, d = rows
    return difference(add(a, d), add(b, c))


def rows_valid(rows, mass=1):
    return all(min(row) >= 0 and sum(row) == mass for row in rows)


def one_visit(rows, mass=1):
    need(
        rows_valid(rows, mass) and not any(defect(rows)),
        "not a one-visit endpoint table",
    )
    c = tuple(map(min, zip(*rows, strict=True)))
    a0 = tuple(min(x, y) for x, y in zip(rows[0], rows[2], strict=True))
    b0 = tuple(min(x, y) for x, y in zip(rows[0], rows[1], strict=True))
    a = (difference(rows[0], a0), difference(rows[2], a0))
    b = (difference(rows[0], b0), difference(rows[1], b0))
    need(all(min(row) >= 0 for row in (c, *a, *b)), "nonnegative lower envelopes")
    need(
        rows == tuple(add(c, a[x], b[y]) for x, y in CONTEXTS),
        "failed converse construction",
    )
    need(
        sum(a[0]) == sum(a[1]) == tv(rows[0], rows[2])
        and sum(b[0]) == sum(b[1]) == tv(rows[0], rows[1]),
        "setting-dependent path weights or nonminimal movement",
    )
    return c, a, b


def finite_converse_census():
    # Independent small positive check: enumerate all three-ticket
    # stocks of deterministic constant/A-only/B-only strategies. No
    # intermediate path frequency is given to the endpoint checker.
    strategies = {tuple(x for _ in CONTEXTS) for x in range(3)}
    for arm, a, b in product((0, 1), range(3), range(3)):
        strategies.add(tuple((a, b)[xy[arm]] for xy in CONTEXTS))
    attained = set()
    for stock in combinations_with_replacement(sorted(strategies), 3):
        attained.add(
            tuple(
                tuple(outcomes.count(o) for o in range(3))
                for outcomes in zip(*stock, strict=True)
            )
        )
    rows = tuple((a, b, 3 - a - b) for a in range(4) for b in range(4 - a))
    passing = {p for p in product(rows, repeat=4) if not any(defect(p))}
    need(
        passing == attained and len(strategies) == 15,
        "finite necessity/converse census",
    )
    for table in passing:
        one_visit(table, 3)
    return {
        "normalized_three_outcome_three_ticket_tables_checked": len(rows) ** 4,
        "one_visit_realizable": len(passing),
        "deterministic_endpoint_strategies": len(strategies),
    }


def scatter(x, ports):
    midpoint = F(2 * sum(x[j] for j in ports), len(ports))
    return tuple(midpoint - a if i in ports else a for i, a in enumerate(x))


def wave_rows():
    signal = scatter((1, 0, 0, 0), H)
    observed = []
    for x, y in CONTEXTS:
        hopped = tuple(
            ((-1) ** x if i == 1 else (-1) ** y if i == 2 else 1) * a
            for i, a in enumerate(signal)
        )
        amplitudes = scatter(hopped, G)
        observed.append(tuple(a * a for a in amplitudes))
    p, q, second_q, second_p = observed
    need(
        rows_valid(observed)
        and p == second_p == tuple(F(i, 81) for i in (9, 4, 4, 64))
        and q == second_q == tuple(F(i, 81) for i in (9, 36, 36, 0)),
        "rational wave parity comparator",
    )
    need(tv(p, q) == p[3] - q[3] == F(64, 81), "one endpoint must attain whole-row TV")
    return tuple(observed)


def fractional_stock(p, q, eps, count):
    """Construct exact sharp nearby table: subnormalized good and bad parts."""
    common = tuple(min(a, b) for a, b in zip(p, q, strict=True))
    res_p, res_q = difference(p, common), difference(q, common)
    r = tv(p, q)
    need(
        r > 0 and count in (3, 4),
        "nontrivial parity model and number of observed contexts",
    )
    slope = 2 if count == 4 else 3
    d = min(eps, r / slope)
    beta = r - slope * d
    if count == 4:
        constant = add(common, scale(add(res_p, res_q), d / r))
        good = (constant,) * 4
    else:
        first = add(common, scale(res_p, 2 * d / r), scale(res_q, d / r))
        middle = add(common, scale(res_p, d / r), scale(res_q, 2 * d / r))
        last = add(common, scale(res_q, 3 * d / r))
        good = (first, middle, middle, last)
    one_visit(good, 1 - beta)
    bad = tuple(scale(res, beta / r) for res in (res_p, res_q, res_q, res_p))
    need(rows_valid(bad, beta), "bad stock mass depends on settings")
    candidate = tuple(add(a, b) for a, b in zip(good, bad, strict=True))
    target = (p, q, q, p)
    need(
        rows_valid(candidate)
        and max(
            tv(a, b) for a, b in zip(candidate[:count], target[:count], strict=True)
        )
        == d,
        "sharp mixture didn't fit requested TV radius",
    )
    # Defect lower bounds use only the named rows; they do not assert
    # equal errors on an unrecorded fourth setting.
    if count == 4:
        need(
            norm_tv(defect(candidate)) == 2 * beta, "four-setting budget not saturated"
        )
    else:
        need(
            candidate[0][3] - candidate[1][3] - candidate[2][3] == beta,
            "three-setting budget not saturated",
        )
    return beta, candidate, good


def vacancy_tags(target):
    """Positive ticket alternative, deliberately NOT a silent-arm model."""
    observed = []
    for x, y in CONTEXTS:
        counts = [0] * 4
        for ticket in range(81):
            if ticket < 17:
                # Fixed common stock, no response from either arm.
                destination = 0 if ticket < 9 else 1 if ticket < 13 else 2
            else:
                occupied_tag, vacancy_tag = 0, 0
                occupied_tag ^= x  # chosen arm is always the first
                vacancy_tag ^= y  # independent wire from the empty arm
                destination = 3 if (occupied_tag ^ vacancy_tag) == 0 else 1 + ticket % 2
            counts[destination] += 1
        observed.append(tuple(F(k, 81) for k in counts))
    need(tuple(observed) == target, "explicit vacancy-wire counterfeit failed")
    return {
        "silent_common_tickets": 17,
        "occupied_plus_vacancy_sensitive_tickets": 64,
        "total_equiprobable_preparation_tickets": 81,
        "chosen_packet_path": "first arm on every ticket",
        "violation": "the second local bit rides a separate tag from a path without the packet; no setting dependence in ticket preparation",
    }


def detector_controls(target):
    efficiency, background = F(3, 4), F(1, 9)
    throughput = efficiency * (1 - background)

    def detector(row):
        # Setting-independent stochastic channel, with dark background
        # replacing the signal outcome exactly in that branch.
        p = scale(row, throughput)
        return (p[0] + background, *p[1:], (1 - background) * (1 - efficiency))

    raw = tuple(detector(p) for p in target)
    need(
        rows_valid(raw) and tv(raw[0], raw[1]) == throughput * tv(target[0], target[1]),
        "fixed independent detector channel",
    )

    # Positive one-visit countercontrol: on ticket A write D unless x=1
    # (loss); on B write E unless y=1 (loss); common ticket always E.
    # Postselecting a click erases a setting-dependent amount of stock.
    counter = []
    for x, y in CONTEXTS:
        outputs = (0 if not x else 2, 1 if not y else 2, 1)
        counter.append(tuple(F(outputs.count(i), 3) for i in range(3)))
    counter = tuple(counter)
    one_visit(counter)
    conditional = tuple(tuple(a / (1 - row[2]) for a in row[:2]) for row in counter)
    need(
        rows_valid(conditional) and defect(conditional)[0] == F(-1, 6),
        "postselection counterfeit missing",
    )
    need(
        not any(defect(tuple(detector((*row, 0)) for row in counter))),
        "common detector noise broke the model identity",
    )
    return {
        "independent_setting_blind_loss_and_dark_background_example": {
            "efficiency": str(efficiency),
            "dark_background": str(background),
            "net_signal_throughput": str(throughput),
            "all_preparation_parity_TV_after_detector_channel": str(tv(raw[0], raw[1])),
        },
        "conditional_click_counterfeit_from_raw_one_visit_table": {
            "raw_D_E_no_click": readable(counter),
            "postselected_D_E": readable(conditional),
            "spurious_conditioned_D_parallelogram_defect": str(defect(conditional)[0]),
        },
    }


def readable(rows):
    return tuple(tuple(map(str, row)) for row in rows)


def probe():
    target = wave_rows()
    p, q, _, _ = target
    r = tv(p, q)
    need(
        norm_tv(defect(target)) == 2 * r
        and target[0][3] - target[1][3] - target[2][3] == r,
        "whole-table and three-context lower bound calibration",
    )
    margins = {}
    for count in (4, 3):
        slope = 2 if count == 4 else 3
        beta, best, _ = fractional_stock(p, q, r / slope, count)
        need(beta == 0, "closest one-visit table must lie in model")
        budgets = []
        for eps in (F(0), r / (2 * slope), r / slope, F(1, 2)):
            needed, _, _ = fractional_stock(p, q, eps, count)
            need(needed == max(0, r - slope * eps), "incorrect sharp non-silent budget")
            budgets.append((str(eps), str(needed)))
        margins[count] = {
            "exact_parity_family_min_non_silent_mass": str(r),
            "closest_one_visit_uniform_TV": str(r / slope),
            "closest_table_completion_including_11": readable(best),
            "tested_sharp_epsilon_non_silent_mass": budgets,
        }
    return {
        "scope": "one exclusive prechosen path, at most one available isolated setting, silent other arm, setting-independent source/detector stock and appropriately defined all-trial endpoint rows",
        "settings_xy": CONTEXTS,
        "full_wave_p00_p01_p10_p11": readable(target),
        "finite_converse_census": finite_converse_census(),
        "endpoint_only_budget": margins,
        "three_setting_event_control": {
            "model_necessary_inequality": "p00(D) <= p10(D) + p01(D)",
            "endpoint_event": "port 3",
            "fixed_coherent_signal_p00_p10_p01": [str(target[i][3]) for i in (0, 2, 1)],
        },
        "positive_raw_vacancy_model": vacancy_tags(target),
        "loss_dark_herald_controls": detector_controls(target),
        "assumptions_and_limits": [
            "No intermediate occupation measurement or assumed fair arm split. Arbitrary occupied-arm hidden updates and shared randomness independent of the joint fresh setting pair are allowed.",
            "A known pre-setting herald or all launched trials is required; keep no-click and any additional outcomes instead of conditioning on signal clicks.",
            "Non-silent mass means a setting-independent share permitted to respond to both bits. Endpoint counts bound that share under this decomposition, not the mechanism or individual leaking trials.",
            "Isolated toggles may still send signals to their common future detector through empty arms, fields, clocks or control buses. Spacelike choice versus choice alone does not forbid that. This is not a Bell test.",
            "Exact rational comparison uses supplied coherent phase control and square-norm endpoint law. Experimental use would require independent isolation and rate/tolerance certification.",
        ],
    }


if __name__ == "__main__":
    print(json.dumps(probe(), sort_keys=True, separators=(",", ":")))
