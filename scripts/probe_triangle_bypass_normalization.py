"""Test total-stock gain by adding a distinguishable untouched branch.

Only *fractions* are read, not an absolute ticket supply. Compare three
outputs with the same detector response law W: input v on a bypass, v+Pv,
and v-Pv. A constant nontrivial bypass fraction p for a given setting means
that its gain is (1-p)/p whenever input stock is positive. This does not
certify dark inputs, untested scales or equal detector response across ports.
"""

from collections import Counter
from fractions import Fraction as F
from itertools import product

from scripts.probe_triangle_exchange_source import (
    initialize,
    need,
    pairs,
    route_block,
    signed_split,
)
from scripts.probe_triangle_stock_rigidity import branches, dark, quadratic, ray, refl


def meter(w, v, k, bypass_gain=1):
    a, b = branches(v, k)
    vals = (bypass_gain * w(v), w(a), w(b))
    total = sum(vals)
    return None if total == 0 else tuple(F(x, total) for x in vals)


def binary(w, v, k):
    pair = tuple(map(w, branches(v, k)))
    return None if not sum(pair) else tuple(F(x, sum(pair)) for x in pair)


def inflated(v):
    # Exactly the same raw weight on every possible analyzer OUTPUT ray.
    # Hence every ordinary two-outcome experiment, including arbitrary
    # repetitions, has identical normalized branch frequencies. Off those
    # rays its total-stock assignment differs.
    return quadratic(v) * (1 if (0 in v or len(set(v)) < 3) else 2)


def mixed(v):
    return quadratic(v) + dark(v)


def hidden(v):
    return quadratic(v) * (1 + int(all(x % 7 == 0 for x in v)))


def addressed(v, k):
    p = refl(k)
    matrix = tuple(
        tuple(int(i == j) for j in range(3)) for i in range(3)
    ) + signed_split(p)
    src = initialize(v)
    for rev in (False, True):
        cloud, routes, gain, _ = route_block(src.cloud, matrix, rev)
        need(
            gain == 5 and set(routes.values()) == pairs(cloud), "bypass ticket coverage"
        )
        # Explicitly trace the old input address and all five descendant seeds.
        events = Counter(
            cloud[routes[addr, s][0]][0] // 3
            for addr in src.tickets.values()
            for s in range(gain)
        )
        need(sum(events.values()) == gain * len(src.tickets), "lost bypass histories")
        read = tuple(F(events[j], sum(events.values())) for j in range(3))
        need(read == meter(quadratic, v, k), "positive ticket output disagrees")


def main():
    for a, b in product(range(-8, 9), repeat=2):
        v = (a, b, -a - b)
        if not quadratic(v):
            continue
        for k in range(3):
            need(
                binary(quadratic, v, k) == binary(inflated, v, k),
                "ordinary analyzer saw hidden stock",
            )
            r = meter(inflated, v, k)
            expected = F(1, 5) if 0 in v or len(set(v)) < 3 else F(1, 3)
            need(r[0] == expected, "protected bypass does not separate")
            # A port that knows the input can counterfeit the whole 3-bin
            # readout. A positive fixed common bypass factor cannot hide two
            # different ratios at different preparations.
            need(
                meter(inflated, v, k, F(quadratic(v), inflated(v)))
                == meter(quadratic, v, k),
                "acceptance-leak countercontrol",
            )
    e = (0, 1, -1)
    m = (2, -1, -1)
    off = (2, 1, -3)
    new = (4, -3, -1)
    for v, k in product((e, m, off, new), range(3)):
        addressed(v, k)
    need(
        all(
            meter(mixed, e, k)[0] == F(2, 7) and meter(mixed, m, k)[0] == F(1, 5)
            for k in range(3)
        ),
        "input-dependent, setting-independent gain",
    )
    need(
        all(
            meter(dark, e, k)[0] == F(1, 2) and meter(dark, m, k) is None
            for k in range(3)
        ),
        "dark is not a successful zero-outcome run",
    )
    # A one-extra-seed experiment and every descendant on the nonzero
    # ray scales 1,2,3,4,5 times 2^a 3^b never reaches a multiple of 7.
    for v, k in product((e, m, off), range(3)):
        need(meter(quadratic, v, k) == meter(hidden, v, k), "subgroup rival not hidden")
        for z in branches(v, k):
            _, scale = ray(z)
            need(not scale or scale % 7 != 0, "initial tested projections hit seven")
    separated = [meter(hidden, new, k)[0] for k in range(3)]
    need(separated == [F(1, 5), F(1, 5), F(13, 114)], "seven-lattice discriminator")
    print(
        "All normalized two-output trines miss an off-ray factor two; "
        "one matched bypass on (2,1,-3) gives 1/5 vs 1/3."
    )
    print(
        "Squared + residue-mod-3 stock: bypass edge 2/7, median 1/5 at every setting. "
        "Pure residue rival gives 1/2 on an edge and no median events."
    )
    print(
        "Hidden factor at multiples of seven survives the first off-ray seed. "
        "(4,-3,-1), last-coordinate setting: 13/114 vs 1/5."
    )
    print(
        "Each old squared-stock ticket has five addressed descendants. Equal port response, "
        "coherent transfer supply and complete branch accounting are apparatus premises."
    )


if __name__ == "__main__":
    main()
