"""Exact finite comparison: run python3 -m scripts.probe_binary_pair_switch_wall.

Every reversible two-bit contact is affine, also when oriented. Embedding it
on named wires and composing a fixed word preserves affinity. Concatenating
independent source and control codewords and common ancillary stock gives XOR
zero across four input corners, hence across every raw output coordinate.
Two distinct clean output codewords for AND would differ on at least one
coordinate, violating that parity. An external nonlinear decoder, correlated
preparation, feedback or setting-dependent word is not covered.

The exchange-symmetric subset preserves Hamming distance at any width. If
two launches retain their disjoint raw inputs unchanged, those inputs already
account for their entire initial distance; initially identical flag wires
cannot also become distinguishable. This does not exclude consumed inputs.

Finite circuit evidence only. Addressed three-site OR toggles with a supplied
zero are an extension, not a simulation by a fixed-clock Rule 54 lattice or
an unlabeled graph contact. No alphabet-wide exclusion or physical derivation.
"""

import json
from fractions import Fraction
from itertools import permutations, product

from scripts import probe_ternary_active_readout as active
from scripts import probe_ternary_vacancy_switch as vacancy


def pair_tables():
    # State x has low and high bit coordinates. Columns are distinct nonzero
    # vectors iff the two-dimensional linear part is invertible over F2.
    gates = set(permutations(range(4)))
    affine = {
        (k, k ^ u, k ^ v, k ^ u ^ v)
        for k in range(4)
        for u, v in permutations((1, 2, 3), 2)
    }
    swap = (0, 2, 1, 3)
    symmetric = {g for g in gates if all(g[swap[i]] == swap[g[i]] for i in range(4))}
    return gates, affine, symmetric


def ternary_flags(source, s, c):
    # Ordinary filled arms are marker vacuum. The two vacancy controls have
    # XOR c. Neither the word nor meter addresses depend on the setting.
    raw = tuple(
        x
        for i in range(2)
        for x in ("T" if s and i == source else "N", *vacancy.stock(i * c))
    )
    return active.compiled_launch(raw, vacancy.switch(0, 1, 3), (0, 3))


def oriented_flags(source, s, c):
    wires = [int(s and i == source) for i in range(2)] + [c]
    for target in (0, 1):
        wires[target] ^= wires[2]
    return tuple(wires[:2])


def rate_certificate(rows):
    rows = tuple(rows)
    if len(rows) != 4 or set(rows) != set(product(range(2), repeat=2)):
        raise ValueError("expected each rectangle corner exactly once")
    target = tuple(s * c for s, c in rows)
    profiles = [
        tuple(k ^ (a * s) ^ (b * c) for s, c in rows)
        for k, a, b in product(range(2), repeat=3)
    ]
    errors = [tuple(x ^ y for x, y in zip(p, target, strict=True)) for p in profiles]
    counts = sorted(map(sum, errors))
    # Every profile misses at least one corner. Setting-independent averaging
    # therefore gives a sum of error rates >= 1, and a maximum >= 1/4.
    sharp = [e for e in errors if sum(e) == 1]
    rates = [Fraction(sum(col), len(sharp)) for col in zip(*sharp, strict=True)]
    # Fixed encodings and fixed word with additive random stock: affine
    # dependence on that stock only complements a fixed output profile with
    # common probability p. Since each profile both succeeds and misses,
    # its worst error is max(p,1-p), minimized at p=1/2.
    if not all({*e} == {0, 1} for e in errors):
        raise AssertionError("fixed-offset certificate lost a witness corner")
    return {
        "mismatch_counts": counts,
        "sharp_errors": rates,
        "offset_minimax": Fraction(1, 2),
    }


def three_toggles(a, b, t):
    state = [a, b, t, 0]
    for left, right in ((0, 1), (0, 3), (1, 3)):
        state[2] ^= state[left] | state[right]
    return tuple(state)


def verify():
    gates, affine, symmetric = pair_tables()
    active.check(gates == affine and len(gates) == 24, "binary affine inventory")
    active.check(
        symmetric == {(0, 1, 2, 3), (0, 2, 1, 3), (3, 2, 1, 0), (3, 1, 2, 0)},
        "signed-coordinate inventory",
    )
    for g in symmetric:
        for x, y in product(range(4), repeat=2):
            active.check((x ^ y).bit_count() == (g[x] ^ g[y]).bit_count(), "distance")
    cert = rate_certificate(product(range(2), repeat=2))
    active.check(
        cert["mismatch_counts"] == [1] * 4 + [3] * 4
        and cert["sharp_errors"] == [Fraction(1, 4)] * 4,
        "mixture bound",
    )
    for src, s, c in product(range(2), repeat=3):
        expected = tuple(int(s and i == (src ^ c)) for i in range(2))
        active.check(ternary_flags(src, s, c) == expected, "ternary raw flags")
        active.check(
            oriented_flags(src, s, c) == (expected if s else (c, c)),
            "one-token oriented countercontrol",
        )
    for a, b, t in product(range(2), repeat=3):
        active.check(
            three_toggles(a, b, t) == (a, b, t ^ (a & b), 0), "addressed Toffoli"
        )
    logical = len(vacancy.switch(0, 1, 3))
    return {
        "binary_pair_permutations": len(gates),
        "exchange_symmetric": len(symmetric),
        "raw_bit_rates": cert,
        "oriented_one_token": {"cnots": 2, "sites": 3, "vacuum_flags_at_c1": [1, 1]},
        "addressed_extension": {"or_toggles": 3, "sites": 4, "supplied_zero": 1},
        "ternary_cost": {
            "logical_contacts": logical,
            "native_contacts": logical * len(active.VACANCY)
            + 2 * len(active.PROTECTED_METER),
            "sites": 6 + 1 + 4,
            "meter_ports": 2,
        },
    }


if __name__ == "__main__":
    print(json.dumps(verify(), indent=2, default=str))
