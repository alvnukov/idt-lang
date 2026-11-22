"""How many observable binary sites and parked units encode the old even masks?

Contract: injectively encode all 16 even five-bit masks V at one constant
weight <=K on m binary sites. Units have no individual labels. Every even XOR
translation must act by a permutation of sites independent of preparation;
an arbitrary decoder is allowed. In the charged version one fixed real
weight per site and a constant read q=6Y=(-2,-2,-2,3,3).x on every input.
Optional symmetry additionally requires every supplied color/weak within-
block relabeling to act by a raw site permutation. No cross-block relabeling
is free by assumption. These are storage/wiring bounds, NOT graph locality,
timing, synthesis cost, lab charge, physical gauge symmetry or chirality.

Proof of lower bound. Each site is a Boolean coordinate function f on V.
The multiset of these functions is stable under translations regardless of
how lifts on redundant sites were chosen. A nonconstant translation orbit
with stabilizer H of codimension c needs >=2^c distinct sites. The sum over
its functions is constant and positive, costing >=1 parked unit on every
input. Its Walsh characters lie in the c-dimensional annihilator H^perp
(translate by h in H). Constants, extra copies, and functions with smaller
Walsh support cannot lower these bounds. Thus the union of the annihilators
must cover every nonzero Walsh component of q. On V the five slot characters
have one dependence, the sum of all five. Each proper c-plane contains at
most c of them. With within-block symmetry the SET of annihilators must also
be stable; merging repeated planes only relaxes the lower bound. We optimize
this relaxation over all subspaces of the exact four-dimensional dual. Raw
encodings below attain the resulting minima, making the bounds sharp.

In particular at m<=11 with <=3 units the only possible covering ranks
are 2,2,1: ranks 4 or 3,2 or 3,1,1 already cost >=12. Each smaller plane
must attain its coverage bound; the unique rank-one plane then singles
out one of the five target characters. S3 x S2 fixes no such character.
For unlimited K a proper-plane cover costs >=2*5 sites (2^c>=2c);
one rank-four plane would cost 16. With no q requirement, injectivity still
requires zero common stabilizer (else two inputs coincide); sum c >=4,
hence >=8 sites. With one unit injection alone requires >=16 sites.
No bound is asserted for hidden addresses, unrestricted updates, additional
ancillas, adjustable weights, or a nonlinear charge decoder.
Run: python3 -B -m scripts.probe_even_carrier_resource_frontier (also with -O).
"""

from collections import Counter, defaultdict
from itertools import permutations

from scripts.probe_chiral_carrier_holdout import EVEN, block
from scripts.probe_five_slot_charge import BENCHMARK, primitive_weights


def need(condition, detail):
    if not condition:
        raise ArithmeticError(detail)


def lift(x):
    return x | ((x.bit_count() % 2) << 4)


V = tuple(lift(x) for x in range(16))  # four independent index bits, not new sites
G = tuple(p + s for p in permutations(range(3)) for s in permutations((3, 4)))
CHARS = (1, 2, 4, 8, 15)
WEIGHTS = primitive_weights(3)


def q(x):
    return sum(w for i, w in enumerate(WEIGHTS) if x & (1 << i))


def perm(x, p):
    return sum(1 << j for i, j in enumerate(p) if x & (1 << i))


def dual_perm(h, p):
    raw = perm(h, p)
    return (raw & 15) ^ (15 if raw & 16 else 0)


def scalar(h, x):
    return (h & x).bit_count() % 2


def spaces():
    zero = frozenset({0})
    seen, stack = {zero}, [zero]
    while stack:
        s = stack.pop()
        for x in range(1, 16):
            ext = s | {x ^ h for h in s}
            if ext not in seen:
                seen.add(ext)
                stack.append(ext)
    need(Counter(map(len, seen)) == {1: 1, 2: 15, 4: 35, 8: 15, 16: 1}, "dual spaces")
    return seen - {zero}


def translated(f, t):
    # Bit j of the 16-bit truth table is f(V[j]); e_i permutes its two halves.
    for k, mask in enumerate((0x5555, 0x3333, 0x0F0F, 0x00FF)):
        if t & (1 << k):
            n = 1 << k
            f = ((f & mask) << n) | ((f >> n) & mask)
    return f


def boolean_orbits(all_spaces):
    # Independent census of every Boolean site function, not just one-hot banks.
    negative = [sum(1 << x for x in range(16) if scalar(h, x)) for h in range(16)]
    seen = set()
    for f in range(1 << 16):
        if f in seen:
            continue
        translates = [translated(f, t) for t in range(16)]
        orb = set(translates)
        seen.update(orb)
        if f in (0, 65535):
            continue
        stabilizer = [t for t, r in enumerate(translates) if r == f]
        annihilator = frozenset(
            h for h in range(16) if all(not scalar(h, t) for t in stabilizer)
        )
        support = {
            h for h in range(16) if f.bit_count() != 2 * (f & negative[h]).bit_count()
        }
        units = [sum((r >> x) & 1 for r in orb) for x in range(16)]
        need(
            annihilator in all_spaces
            and support <= annihilator
            and len(orb) == len(annihilator)
            and len(set(units)) == 1
            and units[0] >= 1,
            "Boolean orbit budget",
        )
    need(len(seen) == 65536, "incomplete function census")


def covering_bounds(all_spaces, symmetric):
    remaining = set(all_spaces)
    dp = {(0, 0): 0}  # (covered target bits, minimum orbit-unit budget) -> sites
    while remaining:
        s = next(iter(remaining))
        orbit = {frozenset(dual_perm(h, p) for h in s) for p in G} if symmetric else {s}
        remaining -= orbit
        scope = set().union(*orbit)
        bits = sum(1 << i for i, h in enumerate(CHARS) if h in scope)
        if not bits:
            continue
        for (b, k), val in tuple(dp.items()):
            key = b | bits, k + len(orbit)
            cost = val + sum(map(len, orbit))
            dp[key] = min(dp.get(key, cost), cost)
    return tuple(
        min(m for (b, k), m in dp.items() if b == 31 and k <= cap)
        for cap in (1, 2, 3, 4, 100)
    )


def banks(masks):
    # Each site has a static address within its bank. Exactly one site is
    # occupied in each bank. Only addresses reachable by an even mask exist.
    sites = [(bank, z) for bank in masks for z in sorted({x & bank for x in V})]
    states = {
        x: frozenset(i for i, (bank, z) in enumerate(sites) if (x & bank) == z)
        for x in V
    }
    return states, [q(z) for _, z in sites]


def compact():
    uvals = (0, 3, 5, 6)
    states = {}
    for x in V:
        v = x >> 3
        u = (x & 7) ^ (7 if v.bit_count() % 2 else 0)
        states[x] = frozenset((uvals.index(u), 4 + v))
    # Any additive raw charge on two one-hot banks factors as A(u)+B(v)+c.
    # The display uses u=000,011, v=00,01, not unseen mask preparations.
    decoder = {code: x for x, code in states.items()}
    samples = [
        q(decoder[frozenset((u, 4 + v))]) for u, v in ((0, 0), (1, 1), (1, 0), (0, 1))
    ]
    need(
        samples == [0, 1, -4, -3] and samples[0] + samples[1] - sum(samples[2:]) == 8,
        "nonadditive rectangle",
    )
    return states


def raw_perm(states, m, target):
    # Raw site i must go to site j with E(x)[i] = E(target(x))[j] on ALL
    # inputs simultaneously. Match duplicate coordinate columns one-to-one.
    available = defaultdict(list)
    for j in range(m):
        col = tuple(j in states[target(x)] for x in V)
        available[col].append(j)
    pi = []
    for i in range(m):
        col = tuple(i in states[x] for x in V)
        if not available[col]:
            return None
        pi.append(available[col].pop())
    need(
        len(set(pi)) == m
        and all({pi[i] for i in states[x]} == states[target(x)] for x in V),
        "physical port witness",
    )
    return tuple(pi)


def check(states, m, k, symmetry, weights=None):
    need(
        set(states) == set(EVEN)
        and len(set(states.values())) == 16
        and all(len(code) == k for code in states.values())
        and set().union(*states.values()) == set(range(m)),
        "decoder/constant weight",
    )
    if weights is not None:
        need(
            all(sum(weights[i] for i in states[x]) == q(x) for x in V), "static charge"
        )
    for t in V:
        need(
            raw_perm(states, m, lambda x, t=t: x ^ t) is not None,
            "XOR lacked a global wire map",
        )
    accepted = sum(
        raw_perm(states, m, lambda x, p=p: perm(x, p)) is not None for p in G
    )
    need((accepted == 12) == symmetry, "within-block permutation contract")


def main():
    need(
        set(V) == set(EVEN)
        and WEIGHTS == (-2, -2, -2, 3, 3)
        and all(q(x) == BENCHMARK[block(x)][3] for x in V),
        "old charge convention",
    )
    walsh = {h: sum(q(x) * (-1) ** scalar(h, x & 15) for x in V) for h in range(16)}
    need(
        {h: w for h, w in walsh.items() if w}
        == dict(zip(CHARS, (16, 16, 16, -24, -24))),
        "nonzero Walsh components of q",
    )
    subspaces = spaces()
    need(
        all(
            len(s & set(CHARS)) <= len(s).bit_length() - 1
            for s in subspaces
            if len(s) < 16
        ),
        "no dependency on a proper subset of target characters",
    )
    boolean_orbits(subspaces)
    bounds = covering_bounds(subspaces, False), covering_bounds(subspaces, True)
    need(
        bounds == ((16, 12, 10, 10, 10), (16, 12, 12, 10, 10)), "resource lower bounds"
    )
    for masks, m, k, sym in [
        ((31,), 16, 1, True),
        ((7, 24), 12, 2, True),
        ((3, 12, 16), 10, 3, False),
        ((1, 2, 4, 24), 10, 4, True),
    ]:
        states, weights = banks(masks)
        check(states, m, k, sym, weights)
        if masks == (7, 24):
            need(
                raw_perm(states, m, lambda x: perm(x, (3, 1, 2, 0, 4))) is None,
                "a cross-block transposition must not be silently granted",
            )
    small = compact()
    check(small, 8, 2, True)
    need(
        raw_perm(small, 8, lambda x: perm(x, (3, 1, 2, 0, 4))) is None,
        "cross-block control on the unsigned eight-site code",
    )
    print("Minimum raw sites for <=1,2,3,4 parked units and all even XOR translations:")
    print(" additive supplied 6Y: 16,12,10,10; plus S3 x S2 by wires: 16,12,12,10.")
    print(
        " Without additive charge: 16,8,8,8; the two-bank 8-site code has charge rectangle 8."
    )
    print(
        "All 16 preparations, translations and block permutations checked on each code."
        " These counts do not derive the five slots, particle readings, gauge or chirality."
    )


if __name__ == "__main__":
    main()
