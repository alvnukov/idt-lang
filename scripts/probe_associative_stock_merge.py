#!/usr/bin/env python3
"""Four-rail associative stock merge: conditional argument and exact finite controls.

Let L={x in Z^n : sum(x)=0}, n>=4. An even, nonnegative, nonzero real
stock W with W(0)=0 is supplied. Every edge ij of a connected graph has a
selector P swapping i,j, a fixed scalar g>0 and two outputs satisfying

    W(Ax) + W(t(I-P)x) = g W(x)                       for EVERY x in L.

The nonzero integer t and g may vary by edge. For A we need only that its
output is unchanged by any transfer k(e_i-e_j) on the input (for a linear
A this is ker A containing that direction). A need not fix spectators,
be scalar on the symmetric sector, or return a particular output label.

Argument over all integers (the executable cuts below are not a Lean proof):

1. W(Px)=W(x): A gives the same output and the other output just negates.
   The physical edge swaps generate all permutations, hence W is symmetric.
   All oriented unit-edge multiples have the same even profile E(m).
2. For one reference edge define F(m)=E(tm)/g. Replace entries a,b by
   a+b,0. Subtracting the two balances cancels the *identical* A output.
   The stock decrement is delta(a,b)=F(a-b)-F(a+b). By symmetry this same
   identity, with the very same F, holds for every pair. This transports
   a stock identity, not a claim that every selector is physically available.
3. Merge a,b,c in either order, using the fourth entry -a-b-c for neutrality.
   The telescopes to (a+b+c,0,0,-a-b-c) give
   delta(a,b)+delta(a+b,c)=delta(b,c)+delta(a,b+c) for all a,b,c.
   At b=c=1: F(a+1)-F(a)-F(a-1)+F(a-2)=F(2). Let u=F(2)/4.
   Subtract u m^2. The remaining first differences are 2-periodic;
   evenness forces their two values to be opposites. With F(0)=0,
   F(m)=u m^2+d 1_{m odd}. No boundedness or continuity was assumed.
4. Parity cancels from delta, so the decrement is -4uab, exactly that
   of 2u sum x_i^2. Successive merges end at zero, hence W=C sum x_i^2/2
   with C=4u>0. Now E(m)=C m^2, so the auxiliary parity freedom is not
   a freedom of W. On any physical edge A(me)=A(0); W(A(0))=0 by its
   zero-input balance. Thus g E(m)=E(2tm) and g=4t^2.

No raw detector, rail, transferable preparation, constant-gain mechanism,
source reversal symmetry, or bypass meter is derived. The argument does
not identify A: once W is quadratic, balance fixes its output norm only.
"""

import argparse
import itertools
import json
from fractions import Fraction
from math import gcd


def require(condition, message):
    if not condition:
        raise AssertionError(message)


def swapped(x, i, j):
    y = list(x)
    y[i], y[j] = y[j], y[i]
    return tuple(y)


def merged(x, i, j):
    y = list(x)
    y[i], y[j] = x[i] + x[j], 0
    return tuple(y)


def split(x, i, j, t=1, twist=False):
    p = swapped(x, i, j)
    a = tuple(t * (v + w) for v, w in zip(x, p))
    b = tuple(t * (v - w) for v, w in zip(x, p))
    if twist:
        k, l = (k for k in range(4) if k not in (i, j))
        a = swapped(a, k, l)
    return a, b


def q(x):
    require(sum(x) == 0, "input must be neutral")
    return sum(z * z for z in x) // 2  # squares sum to an even integer on L


def integer_row(terms):
    # F is even, F(0)=0. Remove cancelled terms before applying the cutoff.
    row = {}
    for n, sign in terms:
        n = abs(n)
        if n:
            row[n] = row.get(n, 0) + sign
    return {n: c for n, c in row.items() if c}


def cocycle(a, b, c):
    # Right merge order minus left; at b=c=1 this is exactly unit_row(a).
    return integer_row(((a-b, -1), (a+b, 1), (a+b-c, -1), (b-c, 1),
                        (b+c, -1), (a-b-c, 1)))


def unit_row(a):
    return integer_row(((a+1, 1), (a, -1), (a-1, -1), (a-2, 1), (2, -1)))


def eval_row(row, profile):
    return sum(c * profile(n) for n, c in row.items())


def insert_row(basis, row):
    # Exact fraction-free sparse elimination, with primitive integer pivots.
    row = dict(row)
    while row:
        pivot = min(row)
        if pivot not in basis:
            basis[pivot] = row
            return
        other = basis[pivot]
        ca, cb = other[pivot], row[pivot]
        row = {k: ca * row.get(k, 0) - cb * other.get(k, 0)
               for k in row.keys() | other.keys()}
        row = {k: v for k, v in row.items() if v}
        if row:
            divisor = gcd(*row.values())
            row = {k: v // divisor for k, v in row.items()}


def rank_cut(k):
    unit, full = {}, {}
    for a in range(2, k):
        require(unit_row(a) == cocycle(a, 1, 1), "unit identity mismatch")
        insert_row(unit, unit_row(a))
    count = 0
    for a, b, c in itertools.product(range(-k, k + 1), repeat=3):
        row = cocycle(a, b, c)
        if not row or max(row) > k:
            continue
        require(eval_row(row, lambda n: n*n) == 0, "quadratic cocycle mismatch")
        require(eval_row(row, lambda n: n % 2) == 0, "parity cocycle mismatch")
        insert_row(full, row)
        count += 1
    require(len(unit) == len(full) == k - 2, "unexpected finite nullity")
    return {"cutoff": k, "unknown_even_samples": k, "nonzero_cocycle_rows": count,
            "unit_rank": len(unit), "full_cut_rank": len(full), "nullity": 2,
            "kernel_basis": ["n^2", "odd(n)"]}


def gains_and_twist():
    edges = ((0, 1, 1), (1, 2, -2), (2, 3, 3))  # connected, unequal raw gains
    count = 0
    for abc in itertools.product(range(-2, 3), repeat=3):
        x = abc + (-sum(abc),)
        for i, j, t in edges:
            a, b = split(x, i, j, t, twist=True)
            y = merged(x, i, j)
            ay, by = split(y, i, j, t, twist=True)
            require(a == ay, "twisted plus no longer coalesces the inputs")
            require(q(a) + q(b) == 4*t*t*q(x), "wrong twisted total")
            require(4*t*t*(q(x)-q(y)) == q(b)-q(by), "wrong merge decrement")
            count += 1
    x = (1, 0, -1, 0)
    ca, cb = split(x, 0, 1)
    ta, tb = split(x, 0, 1, twist=True)
    require(ta != ca and tb == cb and q(ta) == q(ca), "spectator control collapsed")
    return {"selector_inputs": count, "edge_gains": [4, 16, 36], "input": x,
            "canonical_plus": ca, "spectator_twisted_plus": ta, "shared_minus": cb,
            "shared_total_over_input": (q(ta) + q(tb)) // q(x)}


def missing_premises():
    # Fixed gain is essential: four-power stock has varying per-input gain
    # even though conditioning on a click gives normalized fractions on both.
    stocks = lambda x: q(x) ** 2
    ratios = []
    for x in ((1, -1, 0, 0), (1, 0, -1, 0)):
        a, b = split(x, 0, 1)
        ratios.append(Fraction(stocks(a) + stocks(b), stocks(x)))
    require(ratios == [16, 10], "gain drift control collapsed")

    # If the unobserved port can just copy the input (A=I), edge-dark stock
    # W=1_{support>=3} balances every selector at g=1 but is not quadratic.
    dark_edges = lambda x: int(sum(z != 0 for z in x) >= 3)
    # Disconnected selectors can support different weights on components.
    separate = lambda x: x[0]**2 + x[1]**2 + 2*x[2]**2 + 2*x[3]**2
    count = 0
    for abc in itertools.product(range(-2, 3), repeat=3):
        x = abc + (-sum(abc),)
        for i, j in itertools.combinations(range(4), 2):
            a, b = split(x, i, j)
            require(dark_edges(x) + dark_edges(b) == dark_edges(x),
                    "copy-port control failed")
            if (i, j) in ((0, 1), (2, 3)):
                require(separate(a) + separate(b) == 4*separate(x),
                        "disconnected control failed")
        count += 1
    require(dark_edges((1, -1, 0, 0)) == 0 < dark_edges((2, -1, -1, 0)),
            "copy-port nonquadratic witness failed")
    require(separate((1, -1, 0, 0)) != separate((0, 0, 1, -1)),
            "disconnected stock accidentally isotropic")
    return {"four_power_input_gains": [int(r) for r in ratios],
            "control_preparations": count, "copy_port_fixed_gain": 1,
            "disconnected_edge_stocks": [2, 4]}


def four_tag_holdout():
    dark = lambda n: int(n % 3 != 0)
    residual = eval_row(cocycle(-1, 1, 1), dark)
    require(residual == -3, "mod-three holdout changed")
    # A routed port, not a port selected by observing its own click.
    z = (1, -1, 0, 0)
    y, _ = split(z, 1, 2)
    other, target = split(y, 2, 3)
    require(y == (2, -1, -1, 0) and target == (0, 0, -1, 1),
            "addressable four-tag holdout wiring changed")
    return {"mod3_unit_cocycle_residual": residual, "source": z,
            "first_plus_23": y, "second_minus_34": target, "second_plus_34": other,
            "conditional_dark_control": "A dark median and bright unit edge are incompatible "
            "with a nonnegative balanced second split, at any finite gain.",
            "access": "Requires addressable fourth idle rail, transport of the first port "
            "without click postselection (or independent median preparation), verified second "
            "difference output and independent edge brightness. No native substrate claimed."}


def run():
    return {
        "scope": "Conditional integer-lattice argument plus finite executable checks; "
                 "not a Lean proof or a derivation of physical rails, gain or readout.",
        "cuts": [rank_cut(k) for k in (4, 7, 10)],
        "spectator_twist": gains_and_twist(),
        "countercontrols": missing_premises(),
        "four_tag_holdout": four_tag_holdout(),
        "measurement_boundary": "Use a matched bypass at identical exposure, register and "
        "collect both outputs including no-click trials, then freeze one gain per setting "
        "before held-out preparations. Normalized fractions alone cannot test fixed gain. "
        "Without an independent stock readout the balance is a premise, not an observation.",
    }


def main():
    parser = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    parser.add_argument("--json", action="store_true", help="emit the complete evidence packet")
    args = parser.parse_args()
    report = run()
    if args.json:
        print(json.dumps(report, indent=2))
    else:
        print(report["scope"])
        for cut in report["cuts"]:
            print(f"F(1..{cut['cutoff']}): rank {cut['full_cut_rank']}, nullity 2 (square, parity)")
        print("Spectator-twisted outputs preserve the stock, not the raw map.")
        print("Fourth-rail mod-3 cocycle residual: -3; composed routed port: -e34.")
        print(report["measurement_boundary"])


if __name__ == "__main__":
    main()
