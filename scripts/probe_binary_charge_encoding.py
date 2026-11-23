"""Can the scheduled bit rule E implement the *supplied* five-slot collision menu?

Compare flat bijective one-bit-per-slot codes with a clean dual-rail compiler.
Arbitrary fixed site permutations do not affect weight. Nonlinear packet
recodings or an environment retaining the missing residue are not excluded
by the clean direct-code obstruction.
The source menu, packet/slot addresses, order of offers, rail preparations and
readout are inputs. Equality of decoded macro-endpoints is not conservation of
a physical charge at internal steps, natural scheduling, or a physics derivation.
Run: python3 -m scripts.probe_binary_charge_encoding
"""

import json
from dataclasses import dataclass
from itertools import permutations, product

from scripts import probe_binary_unanimous_triples as binary
from scripts import probe_blind_collision_charge as native


@dataclass(frozen=True)
class Channel:
    name: str
    arity: int
    swaps: tuple


def pack(cfg):
    return sum(x << (5*i) for i, x in enumerate(cfg))


def channel(name, arity, update):
    """Non-even inputs get the identity extension; keep ordered native packets."""
    swaps = []
    for cfg in product(native.STATES, repeat=arity):
        dst = update(cfg)
        native.need(all(x in native.INDEX for x in dst) and update(dst) == cfg,
                    "not a native involution")
        a, b = pack(cfg), pack(dst)
        if a < b:
            swaps.append((a, b))
    return Channel(name, arity, tuple(swaps))


def menu():
    for i, j in native.PAIRS:
        yield channel(f"A:{i},{j}", 1, lambda s: (native.shuffle(s[0], i, j),))
        yield channel(f"B:{i},{j}", 2, lambda s: native.exchange(s, i, j))
    _, library = native.ternary_library()
    winner = library[(1, 1, "large", 1)]
    yield channel("C", 3, lambda s: native.fire(s, winner))


def constraints(channels):
    """All placements of each operation among the three fixed packet addresses."""
    layers = {tag: set() for tag in "ABC"}
    for op in channels:
        for placement in permutations(range(3), op.arity):
            for a, b in op.swaps:
                def place(x):
                    return sum(((x >> (5*i)) & 31) << (5*p) for i, p in enumerate(placement))
                pos, neg = place(b & ~a), place(a & ~b)
                layers[op.name[0]].add(tuple(sorted((pos, neg))))
    return layers


def preserves(flips, pos, neg):
    # Complementing a site changes its contribution to the increment from d to -d.
    delta = pos.bit_count() - neg.bit_count()
    correction = (flips & pos).bit_count() - (flips & neg).bit_count()
    return (delta - 2*correction) % 3 == 0


def direct_audit(channels):
    rows = constraints(channels)
    all_codes = range(1 << 15)
    survivors = {tag: {f for f in all_codes if all(preserves(f, p, n) for p, n in layer)}
                 for tag, layer in rows.items()}
    counts = {s: len(set.intersection(*(survivors[t] for t in s)))
              for s in ("A", "B", "C", "AB", "AC", "BC", "ABC")}
    # For a held large slot h, occupied small slot w, and marked packet m,
    # delta = sum(T_j for j != h) - 2*s[m,w], T_j = sum_p s[p,j].
    # Vary m: each small column is uniform. Vary w: both small signs agree (S).
    # Vary h: all large T_j coincide mod 3 and equal S mod 3. Each then has
    # two S signs and one -S sign (the three-equal case has T_j = 0 mod 3).
    predicted = set()
    for minority in product(range(3), repeat=3):
        f = sum(1 << (5*p + j) for j, p in enumerate(minority))
        predicted.update((f, f ^ (len(all_codes)-1)))
    native.need(predicted == survivors["C"], "address-dependent C census")
    _, library = native.ternary_library()
    edges = [s for s in library[(1, 1, "large", 1)] if s[:2] == (0, 0)]
    common = []
    for s in sorted(edges):
        t = native.fire(s, library[(1, 1, "large", 1)])
        delta = [sum(native.germ(y, j) - native.germ(x, j) for x, y in zip(s, t, strict=True))
                 for j in native.PORTS]
        native.need(sorted(delta) == [0, 1, 3, 3, 3] and
                    any(delta[j] == 1 and native.germ(s[2], j) for j in native.SMALL),
                    "unexpected slot increments")
        a, b = pack(s), pack(t)
        common.append(sum(preserves(pack((f, f, f)), b & ~a, a & ~b) for f in range(32)))
    return {"addressed_polarities": len(all_codes), "preserving": counts,
            "common_polarities_passing_each_forward_C_edge": common}


def transposition(a, b, n):
    """Yield Fredkins for one exact n-logical-bit transposition, fixing all else.

    Conjugate by pivot-controlled rail swaps so the endpoints differ only at
    the pivot. Test all n-1 other literals with a chain of clean zero sites:
    Fredkin(flag, literal, zero) puts flag AND literal in the zero site.
    Reverse the chain to restore borrowed literals and zeros.
    """
    diff = [j for j in range(n) if (a ^ b) >> j & 1]
    pivot, *others = diff
    pivot_rail = 2*pivot + ((b >> pivot) & 1)
    align = [(pivot_rail, 2*j, 2*j+1) for j in others]
    yield from align
    literals = [2*j + ((a >> j) & 1) for j in range(n) if j != pivot]
    flag, *tail = literals
    compute = []
    for i, literal in enumerate(tail):
        scratch = 2*n + i
        compute.append((flag, literal, scratch))
        flag = scratch
    yield from compute
    yield flag, 2*pivot, 2*pivot + 1
    yield from reversed(compute)
    yield from reversed(align)


def contact_word(op):
    n = 5*op.arity
    high = 3*n - 2
    for a, b in op.swaps:
        for gate in transposition(a, b, n):
            ports = (*gate, high)
            for i, j, k in binary.FREDKIN:
                yield ports[i], ports[j], ports[k]


def additive_control(active, n):
    """Check for incompatible real site-linear increments on *legal* trajectories.

    Each actual E flip forces the sum of its three site weights to vanish, even
    when arbitrary weights are allowed on all workspace bits. Two active triples
    sharing two sites force their third sites' weights equal. Equal weights on a
    slot's two rails make its logical slope zero on the prepared code.
    """
    witnesses = {}
    for j in range(n):
        for triple in sorted(active):
            if 2*j not in triple or 2*j+1 in triple:
                continue
            other = tuple(sorted((set(triple) - {2*j}) | {2*j+1}))
            if other in active:
                witnesses[j] = [active[triple], active[other]]
                break
    # Requested comparison observable, not an input to contact synthesis.
    def q(mask):
        c, w = native.occ(mask)
        return -2*c + 3*w
    slopes = []
    for j in range(5):
        k, l = [i for i in range(5) if i != j][:2]
        # All three masks and the zero reference are native even masks.
        twice = q(1 << j | 1 << k) + q(1 << j | 1 << l) - q(1 << k | 1 << l) - q(0)
        slopes.append(twice // 2)
    native.need(0 in witnesses and slopes[0] != 0, "missing contradictory real slope")
    return {"forced_zero_rail_slopes": sorted(witnesses), "required_q_slopes": slopes*(n//5),
            "example_step_and_input": witnesses[0]}


def replay(op):
    """Exact bit-sliced E truth table on all 2^n logical inputs simultaneously."""
    n = 5*op.arity
    size = 1 << n
    full = (1 << size) - 1
    # Column j's row x is bit j of x (alternating blocks of length 2^j).
    cols = [(full // ((1 << (1 << j)) + 1)) << (1 << j) for j in range(n)]
    state = [v for col in cols for v in (full ^ col, col)] + [0]*(n-2) + [full]
    expected = state.copy()
    legal = full
    for i in range(op.arity):
        a, b, c, d, e = cols[5*i:5*i+5]
        legal &= full ^ (a ^ b ^ c ^ d ^ e)
    active = {}
    for a, b in op.swaps:
        affected = (1 << a) | (1 << b)
        for j in range(n):
            if (a ^ b) >> j & 1:
                expected[2*j] ^= affected
                expected[2*j+1] ^= affected
    offers = 0
    for i, j, k in contact_word(op):
        equal = full ^ ((state[i] ^ state[j]) | (state[j] ^ state[k]))
        if op.name == "C" and (changed := equal & legal):
            triple = tuple(sorted((i, j, k)))
            if triple not in active:
                active[triple] = (offers+1, (changed & -changed).bit_length()-1)
        state[i] ^= equal
        state[j] ^= equal
        state[k] ^= equal
        offers += 1
    native.need(state == expected, f"{op.name}: raw endpoint or any helper not restored")
    report = {"channel": op.name, "endpoint_pairs": len(op.swaps), "verified_inputs": size,
              "prepared_zero_sites": n-2, "prepared_high_sites": 1, "sites": len(state),
              "E_offers": offers}
    if op.name == "C":
        report["per_step_real_additive_control"] = additive_control(active, n)
    return report


def probe():
    channels = tuple(menu())
    return {"direct": direct_audit(channels), "dual_rail": [replay(op) for op in channels],
            "scope": "Externally addressed and scheduled compilation of specified endpoint maps. "
                     "No primitive charge, natural firing law, or physical interpretation derived."}


if __name__ == "__main__":
    print(json.dumps(probe(), indent=2))
