"""Move refinement scale with each signed mark instead of storing it at a junction.

An address k means a position in a refinement hierarchy, NOT physical time or
a predetermined real amplitude. Opposites on one wire/level cancel, and three
equal signed marks there can be replaced by one at k-1. We work modulo those
relations; discarded branch histories are not invertible. Signed integer
coefficients are shorthand for multiple equal marks, and storage is unbounded.
Only an external comparator uses fractions. No detection, clocks or dynamics
forcing this hierarchy in nature are inferred.
"""

from __future__ import annotations

import json
from fractions import Fraction as F
from itertools import product
from math import gcd


def need(ok, message):
    if not ok:
        raise ArithmeticError(message)


def normal(row):
    """Balanced-ternary local carry on one wire; each output digit is 0, ±1."""
    work, out = dict(row), {}
    while work:
        k = max(work)
        q, t = divmod(work.pop(k) + 1, 3)
        if t != 1:
            out[k] = t-1
        if q:
            work[k-1] = work.get(k-1, 0) + q
    return out


def signed_star(x, h, compress=True):
    """Each incoming unit returns one opposite and sends two to each other arm."""
    if len(h) != 3 or len(set(h)) != 3:
        raise ValueError("three distinct ports required")
    y = [dict(v) if i not in h else {} for i, v in enumerate(x)]
    for i in h:
        for k, z in x[i].items():
            for j in h:
                w = y[j]
                w[k+1] = w.get(k+1, 0) + (-1 if i == j else 2)*z
    for j in h:
        y[j] = normal(y[j]) if compress else {k: z for k, z in y[j].items() if z}
    return y


def read(row, odd_gain=1):
    return sum((z * F(3)**(-k) * (odd_gain if k % 2 else 1) for k, z in row.items()), F())


def ideal(x, h):
    y = list(x)
    m = 2*sum(x[i] for i in h)/F(len(h))
    for i in h:
        y[i] = m-x[i]
    return y


H, G = (0, 1, 2), (1, 2, 3)


def enc(x):
    return [normal({0:z}) for z in x]


def localized_coefficients():
    # Integer permutation-equivariant one-step substitution has a at source,
    # b at each other arm, all at depth +1. Echo means A²=m² I on fixed
    # level, uniform signed transmission means a+(d-1)b=m. Neither is free.
    rows = {}
    trials = 0
    for d in range(2, 13):
        minima = []
        for m in range(1, 19):
            actual = set()
            for a, b in product(range(-m, m+1), repeat=2):
                trials += 1
                if (a+(d-1)*b == m and a*a+(d-1)*b*b == m*m and
                        2*a*b+(d-2)*b*b == 0):
                    actual.add((a, b))
            expected = {(m, 0)}
            if (2*m) % d == 0:
                b = 2*m//d
                expected.add((b-m, b))
                minima.append((m, b-m, b))
            need(actual == expected, "integer substitution classification")
        m, a, b = minima[0]
        need(m == d//gcd(d, 2), "minimal radix")
        rows[d] = [m, a, b, abs(a)+(d-1)*abs(b)]
    return {"searches":trials, "minimal_radix_return_other_and_pre_carry_marks":rows}


def test_words():
    tested = 0
    for seed in ((1, 0, 0, 0), (0, -1, 1, 0), (2, 1, -1, -2), (-3, 0, 2, 7)):
        for n in range(7):
            for word in product((H, G), repeat=n):
                x, ref = enc(seed), list(map(F, seed))
                for h in word:
                    x = signed_star(x, h)
                    ref = ideal(ref, h)
                    need(list(map(read, x)) == ref, "moving depth lost superposition")
                for h in reversed(word):
                    x = signed_star(x, h)
                need(x == enc(seed), "not reversible on the digit quotient")
                tested += 1
    # Rescale-equivalent and canceled preparations cannot affect a later star.
    raw = [{1:6, 2:-9}, {0:-1, 1:3}, {0:2}, {2:1}]
    fixed = [normal(row) for row in raw]
    for h in (H, G):
        need([normal(r) for r in signed_star(raw, h)] == signed_star(fixed, h),
             "contact depends on arbitrary decomposition")
    return tested


def growth():
    e = (1, 0, 0, 0)
    x, ref, samples = enc(e), list(map(F, e)), []
    for n in range(1, 49):
        for h in (H, G):
            x, ref = signed_star(x, h), ideal(ref, h)
        digits = [k for row in x for k in row]
        need(list(map(read, x)) == ref and max(digits) == 2*n and
             max(r.denominator for r in ref) == 9**n, "sharp depth on overlap")
        need(sum(v*v for v in ref) == 1 and len(digits) <= 4*(2*n+1), "storage or norm")
        if n in (1, 2, 4, 8, 16, 32, 48):
            samples.append({"contact_pairs": n, "deepest_level":max(digits), "stored_marks":len(digits)})
    limits = []
    for cap in range(7):
        ref, approx = list(map(F,e)), list(map(F,e))
        for count in range(1, cap+3):
            h = H if count % 2 else G
            ref, approx = ideal(ref, h), ideal(approx, h)
            approx = [F(round(v*3**cap), 3**cap) for v in approx]
            if approx != ref:
                break
        need(approx != ref and count == cap+1, "fixed maximum depth rival")
        limits.append([cap, count, str(sum((a-b)**2 for a,b in zip(ref,approx,strict=True)))])
    return {"growth":samples, "hard_cap_nearest_rounding_first_wrong_gate_and_squared_error":limits}


def underdetermined_calibration():
    # Do not reduce single levels here: only equal-depth cancellation and a
    # *two*-step echo have been offered. A hidden alternating gain is legal.
    seed = enc((1,0,0,0))
    x = signed_star(signed_star(seed,H,False),H,False)
    need(x == [{2:9},{},{},{}], "raw echo")
    need([read(v,2) for v in x] == list(map(read,seed)), "alternative must pass echo")
    x = seed
    for h in (H,G,H):
        x = signed_star(x,h,False)
    calibrated, odd = [read(v) for v in x], [read(v,2) for v in x]
    need(calibrated == [F(11,27),F(-4,27),F(-4,27),F(8,9)], "cross-depth calibration")
    need(odd == [F(19,27),F(-2,27),F(-2,27),F(8,9)], "alternate level-sensitive meter")
    need(read({1:3},2) != read({0:1},2), "one-level refinement must distinguish meter")
    return {"raw_two_step_echo":"9 grandchildren at incident port, all alternatives cancel",
            "three_gate_port_fields_for_standard_vs_doubled_odd_gain":
                [[str(v) for v in row] for row in (calibrated,odd)],
            "distinguishing_preparation":"one mark and three children at the same port; only a one-level calibration equates them"}


def probe():
    return {"scope":"conditional signed multiset rules on a movable hierarchy, no detection or particle physics",
            "substitution":localized_coefficients(), "exact_overlapping_words_and_inverses":test_words(),
            "depth":growth(), "missing_relation":underdetermined_calibration(),
            "cost":"unbounded relative level and local carry, not a finite-state contact or one click per mark"}


if __name__ == "__main__":
    print(json.dumps(probe(), sort_keys=True))
