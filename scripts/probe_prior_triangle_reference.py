"""Set up two reference triangles before either local preparation choice.

The reference contact and feedback are supplied, not a pair of independent
finished-package sources. Ports pick their own settings and prepare *after*
distribution. Co-location for the final exchange, label identification and
consistent relative winding are also supplied. Finite matched paths only.

Run: python3 -B -O -m scripts.probe_prior_triangle_reference
"""

from collections import Counter, defaultdict
from fractions import Fraction as F
from functools import cache
from itertools import product

from scripts.probe_triangle_cycle_phase_axis import (
    BITS,
    LABELS,
    SETTINGS,
    D,
    K,
    cycle_paths,
    edge,
    gain,
    independent,
    need,
    observed_table,
    rank,
    read,
    signed_vector,
    transposition,
)
from scripts.probe_triangle_exchange_source import (
    Stock,
    norm,
    route_block,
    signed_split,
)
from scripts.probe_triangle_reference_sewing import (
    GRID,
    SWAP_FULL,
    detector,
    exchange,
    index,
    outer,
    preparations,
)


def fix_reference(refs):
    """Perform the contact feedback once, before any choices or data stocks."""
    cloud = []
    for rail, sign in refs.cloud:
        h, rs = divmod(rail, 9)
        r, s = divmod(rs, 3)
        cloud.append((9 * h + 3 * r + (transposition(0)[s] if h == 0 else s), sign))
    return Stock(tuple(cloud), refs.tickets.copy())


def package_source(refs, data, k, l):
    """Attach *actual* independent data tickets to both prior contact branches.

    A setting-dependent cyclic permutation of each fixed edge gives the
    adjacent edge used in the single-port preparation. No reference changes.
    """
    cloud = []
    for rail, sign in refs.cloud:
        h, rs = divmod(rail, 9)
        r, s = divmod(rs, 3)
        for ab, t in data.cloud:
            a, b = divmod(ab, 3)
            a = (a + (k + 1 if k in D else 0)) % 3
            b = (b + (l + 1 if l in D else 0)) % 3
            cloud.append((81 * h + index(a, r, b, s), sign * t))
    n = len(data.cloud)
    return Stock(
        tuple(cloud),
        {
            (*t, *u): (i * n + p, j * n + q)
            for t, (i, j) in refs.tickets.items()
            for u, (p, q) in data.tickets.items()
        },
    )


@cache
def move(party, setting):
    out = []
    for xyz in GRID:
        v = list(xyz)
        i = 2 * party
        if setting == K:
            v[i], v[i + 1] = (v[i] + 1) % 3, (v[i + 1] + 1) % 3
        else:
            v[i] = transposition(setting)[v[i]]
        out.append(index(*v))
    return tuple(out)


@cache
def orbits(m):
    """Each local mixer touches one orbit; a recorded history is never mixed."""
    result, seen = [], set()
    for i in range(81):
        if i in seen:
            continue
        orbit = []
        while i not in seen:
            seen.add(i)
            orbit.append(i)
            i = m[i]
        need(i == orbit[0] and len(orbit) in (1, 2, 3), "invalid path orbit")
        result.append(tuple(orbit))
    return tuple(result)


@cache
def small_gate(n):
    if n in (1, 2):
        return signed_split((0,) if n == 1 else (1, 0))
    # Restrict the old 9-rail comparison to a complete simultaneous orbit.
    diag = (0, 4, 8)
    whole = cycle_paths(1, (1, 1))
    return tuple(tuple(whole[9 * h + i][j] for j in diag) for h in BITS for i in diag)


@cache
def local_route(w):
    """Canonical live-address order inside a mixer; no rescaling or renormalizing."""
    chunk = tuple(
        (i, 1 if x > 0 else -1) for i, x in enumerate(w) for _ in range(abs(x))
    )
    raw, routes, g, _ = route_block(chunk, small_gate(len(w)))
    need(g == (9 if len(w) == 3 else 4), "seed gain")
    return raw, routes, g


def routed(s, m):
    orbit_list = orbits(m)
    locate = {r: (u, p) for u, o in enumerate(orbit_list) for p, r in enumerate(o)}
    groups = defaultdict(list)
    for ident, (rail, sign) in enumerate(s.cloud):
        h, r = divmod(rail, 81)
        u, p = locate[r]
        groups[h, u].append((p, ident, sign))
    cloud, lookup, routers = [], {}, {}
    for (h, u), chunk in groups.items():
        o = orbit_list[u]
        w = [0] * len(o)
        for j, (p, ident, sign) in enumerate(sorted(chunk)):
            w[p] += sign
            lookup[ident] = (h, u), j
        need(sum(map(abs, w)) == len(chunk), "uncancelled input")
        raw, routes, g = local_route(tuple(w))
        base = len(cloud)
        for v, sign in raw:
            b, p = divmod(v, len(o))
            cloud.append((81 * (2 * h + b) + o[p], sign))
        routers[h, u] = base, routes, g
    tickets = {}
    for t, (a, b) in s.tickets.items():
        key, i = lookup[a]
        key2, j = lookup[b]
        need(key == key2 and s.cloud[a][0] == s.cloud[b][0], "mixed input event")
        base, routes, g = routers[key]
        for seed in range(g):
            x, y = routes[(i, j), seed]
            dest = base + x, base + y
            rail = cloud[dest[0]][0]
            need(
                rail == cloud[dest[1]][0] and rail // 162 == key[0], "lost input herald"
            )
            tickets[(*t, seed)] = dest
    rail_counts = Counter(i for i, _ in cloud)
    need(
        len(tickets)
        == len(set(tickets.values()))
        == sum(x * x for x in rail_counts.values()),
        "descendants not bijective onto ordered same-rail pairs",
    )
    return Stock(tuple(cloud), tickets)


def counts(s):
    return Counter(s.cloud[a][0] // 81 for a, _ in s.tickets.values())


def fast(v, party, setting):
    """Independent replay of signed children for the alternative local readouts."""
    m = move(party, setting)
    if setting != K:
        return exchange(v, m)
    plus = tuple(x + v[j] + v[m[j]] for x, j in zip(v, m, strict=True))
    return plus, tuple(3 * x - y for x, y in zip(v, plus, strict=True))


def prep_fraction(k, b):
    return F(1, 2) if k == K else (F(3, 4), F(1, 4))[b]


def local_effects(v, left, right, base):
    """All 16 local-setting pairs and all four outcomes, including zeros."""
    total = norm(v)
    cells = Counter()
    for k, l in product(SETTINGS, repeat=2):
        den = total * gain(k) * gain(l)
        subtotal = 0
        for a, w in enumerate(fast(v, 0, k)):
            for b, z in enumerate(fast(w, 1, l)):
                n = norm(z)
                need(
                    F(n, den) == base[left + (k, a)] * base[right + (l, b)],
                    "local readouts do not factor within the recorded preparation",
                )
                cells[bool(n)] += 1
                subtotal += n
        need(subtotal == den, "lost a joint local readout")
    return cells


def probe():
    # Contact precedes every iteration over settings. Both flags survive, with
    # different actual prior addresses. No data carrier takes part in contact.
    raw_refs = read(independent(edge(0), edge(0)), K, 1)
    refs = fix_reference(raw_refs)
    data = independent(edge(0), edge(0))
    rv = signed_vector(refs, 18)
    need(len(refs.tickets) == 36 and len(data.tickets) == 4, "wrong initial tickets")
    for h in BITS:
        v = rv[9 * h : 9 * (h + 1)]
        upper = cycle_paths(1, (1, 1))[:9]
        need(
            norm(v) == 18
            and all(
                sum(a * b for a, b in zip(row, v, strict=True)) == 0 for row in upper
            ),
            "feedback did not lock both flags to minus",
        )
        need(rank([v[i : i + 3] for i in (0, 3, 6)]) == 2, "reference pair factored")
    base = observed_table()
    antis, cells, errors = Counter(), Counter(), Counter()
    prep_cells = Counter()
    # Hidden cyclic turns AFTER the two local packets are prepared. The
    # receiver neither reads nor corrects them in the comparator.
    turns = [
        tuple(index(x, (r - u) % 3, y, (s - v) % 3) for x, r, y, s in GRID)
        for u, v in product(D, repeat=2)
    ]
    for k, l in product(SETTINGS, repeat=2):
        s = package_source(refs, data, k, l)
        need(counts(s) == {0: 72, 1: 72}, "reference flag or data stock changed")
        prepared = routed(routed(s, move(0, k)), move(1, l))
        before, after = counts(prepared), counts(routed(prepared, SWAP_FULL))
        vec = signed_vector(prepared, 8 * 81)
        nofix = signed_vector(package_source(raw_refs, data, k, l), 2 * 81)
        for h, a, b in product(BITS, repeat=3):
            hist = 4 * h + 2 * a + b
            mass = before[hist]
            need(
                F(mass, 72 * gain(k) * gain(l))
                == prep_fraction(k, a) * prep_fraction(l, b),
                "preparation heralds failed to factor on an initial flag",
            )
            v = vec[81 * hist : 81 * (hist + 1)]
            need(
                norm(v) == mass and rank([v[i : i + 9] for i in range(0, 81, 9)]) == 2,
                "unexpected raw package rank or population",
            )
            target = (1 - base[k, a, l, b]) / 2
            need(
                after[2 * hist] + after[2 * hist + 1] == 4 * mass
                and F(after[2 * hist + 1], 4 * mass) == target,
                "whole-package comparator",
            )
            for turn in turns:
                turned = tuple(v[i] for i in turn)
                need(
                    F(norm(exchange(turned, SWAP_FULL)[1]), 4 * mass) == target,
                    "post-preparation independent cyclic turns changed the whole swap",
                )
            antis[h, target] += 1
            prep_cells[h, mass] += 1
            cells.update(
                {
                    (h, sign): n
                    for sign, n in local_effects(v, (k, a), (l, b), base).items()
                }
            )
            # Same source and local paths, with only the *prior* feedback removed.
            x = fast(fast(nofix[81 * h : 81 * (h + 1)], 0, k)[a], 1, l)[b]
            uncorrected = F(norm(exchange(x, SWAP_FULL)[1]), 4 * norm(x))
            errors[h, uncorrected - target] += 1
            if (k, a, l, b, h) == (0, 0, K, 0, 0):
                need((uncorrected, target) == (F(3, 4), F(1, 4)), "uncorrected witness")
    need(
        all(cells[h, False] == 960 and cells[h, True] == 3136 for h in BITS),
        "local product cell coverage",
    )
    need(
        errors
        == {
            (0, F(0)): 44,
            (0, F(1, 8)): 8,
            (0, F(3, 8)): 8,
            (0, F(1, 2)): 4,
            (1, F(0)): 64,
        },
        "uncorrected control",
    )
    # Opposite time ordering: finish both packages independently, then meet
    # their references. This control is NOT the correlated source above.
    src = preparations()
    for (k, a), (l, b) in product(LABELS, repeat=2):
        p, uncond, _, _ = detector(outer(src[k, a, 0], src[l, b, 0]))
        target = (1 - base[k, a, l, b]) / 2
        need(p == target and uncond == target / 2, "late-contact control")
    return antis, prep_cells, errors


def main():
    antis, prep_cells, _ = probe()
    for h in BITS:
        print(
            "Prior flag",
            ("+", "-")[h],
            "; prep ticket mass:cells",
            sorted((m, n) for (v, m), n in prep_cells.items() if v == h),
            "; antiswap:cells",
            sorted((str(p), n) for (v, p), n in antis.items() if v == h),
        )
    print(
        "64/64 exact whole-package comparisons per prior flag; every preparation herald retained."
    )
    print(
        "All nine independent cyclic reference turns preserve the whole-swap table on each flag."
    )
    print(
        "Per flag: 3136 positive and 960 zero joint local readings; all factor. Raw joint currents have package-matrix rank 2 in every cell."
    )
    print(
        "No correction: 20/64 mismatches on +, none on -; P0+ / K+ gives 3/4 rather than 1/4 on +."
    )
    print(
        "Already independent finished packages: late reference minus is fair, exact only on that branch."
    )
    print(
        "Supplied prior contact, conditional reflection, label/winding conventions and final co-location; no independent finished-package sources."
    )


if __name__ == "__main__":
    main()
