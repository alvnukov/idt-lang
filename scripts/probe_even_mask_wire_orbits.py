"""Exact raw-site cost of OPTIONAL input-independent rewiring symmetries on 16 even masks.

V is the 16-element even subspace of five labelled bits. A codeword is a
fixed-weight subset of m raw sites (identical units, at most one per site).
Require an injective code and for each logical generator g some permutation
of sites carrying EVERY codeword C(x) to C(gx). No logical coordinate need
be a raw site. No consistency of the chosen rewires off the code is assumed.

Each raw site has a membership function f:V->Bool. Any such rewire preserves
their multiset under f -> f o g^-1. Conversely, an invariant multiset gives
actual rewires by permuting these functions and equally numbered copies. So
all sites decompose as full function orbits with fixed multiplicities. V acts
transitively: an orbit O costs |O| sites and uses |O|*weight(f)/16 units on
EVERY mask. Duplicate copies and constants never separate a new pair; they
can be deleted for upper occupancy budgets and minimization of raw sites.

For a union of orbits, the positions indistinguishable from zero are the
intersection of the orbit kernels; equivalence is translation invariant, so
the code separates every pair iff only zero lies in that intersection.
Dynamic programming below exhausts orbit choices (not only affine functions).
Independent lower check: on distinct site functions an individual V-orbit
has size 2^r for r the codimension of its translation stabilizer. An injective
union has intersection of these stabilizers zero, so sum r >= 4 and
m >= sum 2^r >= 2*sum r >= 8. With one unit, m>=16 by counting codewords.

The all-five S5 symmetry is a separate assumption, not required by an
externally specified 3+2 split, and is not a gauge group or a matter
derivation. Only finite code resources under these exact contracts are tested.
Run: python3 -B -m scripts.probe_even_mask_wire_orbits [--emit-orbits GROUP].
"""

import argparse
import json
from collections import Counter
from dataclasses import dataclass
from itertools import permutations


MASKS = tuple(x for x in range(32) if x.bit_count() % 2 == 0)
INDEX = {x: i for i, x in enumerate(MASKS)}
ALL = (1 << len(MASKS)) - 1
GROUPS = {"all_five": (0, 1, 2, 3), "three_plus_two": (0, 1, 3), "translations": ()}
CAP = 5


def need(test, why):
    if not test:
        raise AssertionError(why)


def truth(predicate):
    return sum(1 << i for i, x in enumerate(MASKS) if predicate(x))


def generators(group):
    gens = [tuple(INDEX[x ^ (1 << k) ^ 16] for x in MASKS) for k in range(4)]
    for k in GROUPS[group]:
        gens.append(tuple(INDEX[x ^ ((3 << k) if ((x >> k) ^ (x >> (k+1))) & 1 else 0)]
                          for x in MASKS))
    for p in gens:
        need(sorted(p) == list(range(16)) and all(p[p[j]] == j for j in range(16)), "not an involution")
    return gens


def bitlut(p):
    """Permute a full truth table's 16 bit positions through two byte lookups."""
    parts = []
    for offset in (0, 8):
        t = [0]*256
        for x in range(1, 256):
            bit = x & -x
            t[x] = t[x ^ bit] | (1 << p[offset + bit.bit_length()-1])
        parts.append(t)
    return parts


@dataclass(frozen=True)
class Orbit:
    representative: int
    sites: int
    occupancy: int
    kernel: int  # bit i = this orbit cannot distinguish MASKS[i] from zero


def enumerate_orbits(gens):
    maps = [bitlut(p) for p in gens]
    unseen = bytearray([1]) * 65536
    records, cheap = [], {}
    for f in range(65536):
        if not unseen[f]:
            continue
        words = [f]
        unseen[f] = 0
        for v in words:
            for lo, hi in maps:
                u = lo[v & 255] | hi[v >> 8]
                if unseen[u]:
                    words.append(u)
                    unseen[u] = 0
        sites = len(words)
        ones, remainder = divmod(sites*f.bit_count(), 16)
        need(remainder == 0, "nonintegral constant weight")
        kernel = ALL
        for v in words:
            kernel &= v if v & 1 else v ^ ALL
        record = Orbit(f, sites, ones, kernel)
        records.append(record)
        if f not in (0, ALL) and ones <= CAP:
            cheap[f] = tuple(sorted(words))
            # Independent literal occupancy and separation checks for usable orbits.
            signatures = [tuple((v >> i) & 1 for v in words) for i in range(16)]
            need(all(sum(s) == ones for s in signatures), "actual orbit occupancy differs")
            need(all((signatures[i] == signatures[j]) == bool(kernel & (1 << INDEX[x^y]))
                     for i, x in enumerate(MASKS) for j, y in enumerate(MASKS)), "wrong pair kernel")
    need(sum(r.sites for r in records) == 65536 and not any(unseen), "incomplete truth-table partition")
    return records, cheap


def checked_code(words, gens):
    # Construct the actual induced permutations, not just matching weights.
    mapped = {f: j for j, f in enumerate(words)}
    need(len(mapped) == len(words), "unexpected duplicate site")
    signatures = [tuple(j for j, f in enumerate(words) if f >> i & 1) for i in range(16)]
    need(len(set(signatures)) == 16 and len({len(s) for s in signatures}) == 1, "not an injective stock")
    for p in gens:
        site_perm = [mapped[sum(1 << p[k] for k in range(16) if f >> k & 1)] for f in words]
        need(sorted(site_perm) == list(range(len(words))) and
             all(tuple(sorted(site_perm[j] for j in signatures[i])) == signatures[p[i]] for i in range(16)),
             "generator's raw rewire does not carry all codewords")
    return len(words), len(signatures[0])


def all_minima(records, cheap, gens):
    # State = (used units, remaining indistinguishable translations); retain cheapest witness.
    best = {(0, ALL): (0, ())}
    for r in records:
        if r.representative not in cheap:
            continue
        for (used, old_kernel), (cost, reps) in list(best.items()):
            w = used + r.occupancy
            key = w, old_kernel & r.kernel
            if w <= CAP and (key not in best or cost+r.sites < best[key][0]):
                best[key] = cost+r.sites, reps+(r.representative,)
    out = []
    for bound in range(1, CAP+1):
        cost, used, reps = min((c, w, reps) for (w, k), (c, reps) in best.items() if w <= bound and k == 1)
        words = tuple(f for rep in reps for f in cheap[rep])
        need(checked_code(words, gens) == (cost, used), "optimizing witness failed")
        out.append({"max_units": bound, "min_sites": cost, "used_units": used, "orbit_reps": reps})
    return out


def split_quotient_code():
    # Encode weak pair w directly as one of four sites, and even-color triple
    # c' = c + parity(w)*111 as one of a second four. Joint observation
    # recovers (c,w); within-group permutations and even translations rewire both.
    def weak(x):
        return x >> 3

    def even_color(x):
        return (x & 7) ^ (7 if weak(x).bit_count() % 2 else 0)

    return ([truth(lambda x: weak(x) == label) for label in range(4)] +
            [truth(lambda x: even_color(x) == label) for label in (0, 3, 5, 6)])


def burnside(group):
    """Independent orbit totals by truth-table weight from all affine element cycles."""
    totals, order = [0]*17, 0
    for p in permutations(range(5)):
        if group == "translations" and p != tuple(range(5)):
            continue
        if group == "three_plus_two" and set(p[:3]) != {0, 1, 2}:
            continue
        rotated = [sum(((x >> i) & 1) << p[i] for i in range(5)) for x in MASKS]
        for shift in MASKS:
            motion = [INDEX[y ^ shift] for y in rotated]
            remaining = set(range(16))
            fixed = [1]+[0]*16
            while remaining:
                i = min(remaining)
                length = 0
                while i in remaining:
                    remaining.remove(i)
                    i = motion[i]
                    length += 1
                # Each invariant binary function is constant on every cycle.
                for j in range(16, length-1, -1):
                    fixed[j] += fixed[j-length]
            totals = [a+b for a, b in zip(totals, fixed)]
            order += 1
    need(all(t % order == 0 for t in totals), "nonintegral orbit count")
    return order, [t//order for t in totals]


def summarize(group):
    gens = generators(group)
    records, cheap = enumerate_orbits(gens)
    order, expected = burnside(group)
    by_weight = Counter(r.representative.bit_count() for r in records)
    need([by_weight[w] for w in range(17)] == expected, "independent cycle orbit counts disagree")
    minima = all_minima(records, cheap, gens)
    singleton = [1 << i for i in range(16)]
    dual = [truth(lambda x: (x >> k) & 1 == bit) for k in range(5) for bit in (0, 1)]
    need(checked_code(singleton, gens) == (16, 1) and checked_code(dual, gens) == (10, 5), "direct controls")
    if group == "all_five":
        need([r["min_sites"] for r in minima] == [16,16,16,16,10] and
             [set(v) for v in cheap.values() if len(v) == 10] == [set(dual)], "full symmetry census")
        need(all(r.kernel == 1 for r in records if r.representative not in (0, ALL)),
             "nonconstant full-symmetry orbit failed to separate")
        split = set(split_quotient_code())
        # Exchange the last color with the first weak coordinate. At least
        # one transformed site function is entirely absent, so no rewire
        # of the eight raw sites can implement this exchange on the code.
        cross = gens[4+2]
        need(any(sum(1 << cross[k] for k in range(16) if f >> k & 1) not in split for f in split),
             "three-plus-two quotient unexpectedly realizes the cross-block swap")
    else:
        need(checked_code(split_quotient_code(), gens) == (8, 2) and
             [r["min_sites"] for r in minima] == [16,8,8,8,8], "weaker symmetry census")
    eligible = Counter((r.sites, r.occupancy, r.kernel.bit_count()) for r in records if r.representative in cheap)
    return records, {"group": group, "group_order": order, "total_functions": 65536,
                     "orbits_including_constants": len(records), "orbits_by_site_function_weight": expected,
                     "eligible_nonconstant_orbits": len(cheap), "minima": minima,
                     "eligible_profile": [{"sites": m, "units": u, "zero_class_size": z, "orbits": count}
                                          for (m, u, z), count in sorted(eligible.items())]}


def main():
    p = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    p.add_argument("--emit-orbits", choices=GROUPS)
    group = p.parse_args().emit_orbits
    if group:
        records, summary = summarize(group)
        out = {"schema": "idt-even-mask-membership-orbits/1", "mask_order": MASKS, "summary": summary,
               "orbit_columns": ["least_truth_table", "site_count", "units_per_word", "zero_class_bits"],
               "orbits": [[r.representative, r.sites, r.occupancy, r.kernel] for r in records]}
    else:
        out = {"scope": "fixed-weight subsets of binary sites; supplied even translations and named coordinate "
                        "symmetry; no hypercharge, gauging or matter inference", "mask_order": MASKS,
               "groups": [summarize(g)[1] for g in GROUPS]}
    print(json.dumps(out, separators=(",", ":")))


if __name__ == "__main__":
    main()
