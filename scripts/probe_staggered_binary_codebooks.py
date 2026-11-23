"""Site-dependent codes in an unclocked binary E component census.

Each site uses an injection (T,a,b) into two physical bits. Each edge sees
four data bits and its own stock bit; any subset of their ten triples is
allowed. E flips a unanimous triple (000 <-> 111); all moves are optional
and may repeat in any order. Helpers start AND end at their own fixed stocks;
noncode states, dirty helpers, and intermediate clean visits are unrestricted.
Only connected pairs of distinct clean words are compared. This neither
implements individual steps nor supplies a clock, code selector or detector.

Colex bit order: sorted triples (k,j,i) with i outermost, then j<i, k<j.
Local slots 0,1 are left data; 2,3 are right data; 4 is a private helper.
An edge recipe is (template_mask, initial_and_final_helper_bit).
Run: python3 -m scripts.probe_staggered_binary_codebooks [--recipes]
"""

import argparse
from collections import Counter
from functools import lru_cache
from itertools import combinations, permutations, product
import json


def swap_rails(i):
    return (i >> 1) | ((i & 1) << 1)


# Each site's consistent rail swap permutes triples on BOTH incident edges.
BOOKS = tuple(b for b in permutations(range(4), 3) if b <= tuple(map(swap_rails, b)))
TRIPLES = tuple((k, j, i) for i in range(5) for j in range(i) for k in range(j))


def compatible(i, j):
    """Necessary differences mod 3 for clean Ta~aT and aa~bb respectively.

    Every E move changes total binary weight by +/-3. Thus along a connected
    graph dT is constant and db alternates sign. An odd cycle forces db=0;
    this filter is not a sufficient condition for any compilation.
    """
    t, a, b = map(int.bit_count, BOOKS[i])
    u, c, d = map(int.bit_count, BOOKS[j])
    return (t - a - (u - c)) % 3 == 0 and (b - a + d - c) % 3 == 0


@lru_cache(maxsize=None)
def words(n):
    return tuple(map("".join, product("Tab", repeat=n)))


SWAP = {"aa": "bb", "bb": "aa", "Ta": "aT", "aT": "Ta"}


def native_neighbors(x):
    for i in range(len(x)-1):
        z = SWAP.get(x[i:i+2])
        if z is not None:
            yield x[:i] + z + x[i+2:]


@lru_cache(maxsize=None)
def native_components(n):
    """Literal native adjacent substitutions; no site encoding is used."""
    unseen = set(words(n))
    groups = []
    for w in words(n):
        if w not in unseen:
            continue
        unseen.remove(w)
        group = [w]
        for x in group:
            for y in native_neighbors(x):
                if y in unseen:
                    unseen.remove(y)
                    group.append(y)
        groups.append(tuple(group))
    return tuple(groups)


@lru_cache(maxsize=None)
def codes(books):
    return tuple(sum(x << (2*j) for j, x in enumerate(p))
                 for p in product(*(BOOKS[i] for i in books)))


def raw_components(books, recipes):
    """Traverse full raw E-closures from clean seeds, projecting only at end."""
    n = len(books)
    if len(recipes) != n-1:
        raise ValueError("one oriented recipe per edge is required")
    moves = set()
    clean_stock = 0
    for edge, (mask, h) in enumerate(recipes):
        slots = (2*edge, 2*edge+1, 2*edge+2, 2*edge+3, 2*n+edge)
        clean_stock |= h << slots[4]
        moves.update(sum(1 << slots[j] for j in t)
                     for bit, t in enumerate(TRIPLES) if (mask >> bit) & 1)
    clean = {x | clean_stock: w for x, w in zip(codes(books), words(n))}
    visited = bytearray(1 << (3*n-1))
    groups = []
    for seed in clean:
        if visited[seed]:
            continue
        visited[seed] = 1
        group, queue = [], [seed]
        for x in queue:
            if x in clean:
                group.append(clean[x])
            for move in moves:
                if x & move in (0, move):
                    y = x ^ move
                    if not visited[y]:
                        visited[y] = 1
                        queue.append(y)
        groups.append(tuple(group))
    return tuple(groups)


@lru_cache(maxsize=None)
def native_labels(n):
    return {w: i for i, g in enumerate(native_components(n)) for w in g}


def pairs_in(size):
    return size*(size-1)//2


def compare(books, recipes):
    """Counts of missing/extra unordered clean pairs plus one excess witness."""
    n = len(books)
    labels = native_labels(n)
    raw = raw_components(books, recipes)
    both = raw_count = 0
    witness = None
    for group in raw:
        by_native = Counter(labels[w] for w in group)
        both += sum(pairs_in(v) for v in by_native.values())
        raw_count += pairs_in(len(group))
        if len(by_native) > 1 and witness is None:
            witness = (group[0], next(w for w in group if labels[w] != labels[group[0]]))
    native_count = sum(pairs_in(len(g)) for g in native_components(n))
    return native_count-both, raw_count-both, witness


def local_fits():
    """All ten-triple masks and both stocks; build each raw partition once.

    For each of 1024 masks, extend a previous partition by precisely one
    unanimous triple's four links. A disjoint set of nine code pairs is
    exact iff all seven native classes are intact and remain distinct.
    """
    fits = {k: [] for k in product(range(12), repeat=2) if compatible(*k)}
    orders = {k: codes(k) for k in fits}
    # TT, Ta, Tb, aT, aa, ab, bT, ba, bb in this enumeration order.
    reps = (0, 1, 2, 4, 5, 6, 7)
    base = list(range(32))
    partitions = [base]
    for mask in range(1024):
        if mask:
            bit = mask & -mask
            link = sum(1 << i for i in TRIPLES[bit.bit_length()-1])
            part = partitions[mask ^ bit].copy()
            for x in range(32):
                if x & link:
                    continue
                a, b = part[x], part[x | link]
                if a != b:
                    part = [a if v == b else v for v in part]
            partitions.append(part)
        else:
            part = base
        for h in (0, 1):
            for key, order in orders.items():
                c = [part[x | (h << 4)] for x in order]
                if c[1] == c[3] and c[4] == c[8] and len({c[i] for i in reps}) == 7:
                    fits[key].append((mask, h))
    return fits


@lru_cache(maxsize=1)
def training():
    fits = local_fits()
    triples = [b for b in product(range(12), repeat=3) if b[:2] in fits and b[1:] in fits]
    survivors = []
    adjudicated = 0
    for books in triples:
        for left, right in product(fits[books[:2]], fits[books[1:]]):
            loss, extra, _ = compare(books, (left, right))
            if loss:
                raise AssertionError("isolated native moves must lift at fixed exterior")
            adjudicated += 1
            if not extra:
                survivors.append((books, left, right))
    return dict(books_by_pair=fits, compatible_book_triples=len(triples),
                fitted_recipe_pairs=adjudicated, survivors=tuple(survivors))


def tile(books, left, right, n, phase):
    """Only repeat the SAME oriented AB and BA masks/stocks. No refitting."""
    if books[0] != books[2] or phase not in (0, 1):
        raise ValueError("expected alternating training triple and binary phase")
    return (tuple(books[(i+phase) % 2] for i in range(n)),
            tuple((left, right)[(i+phase) % 2] for i in range(n-1)))


def heldouts(survivors):
    rows = []
    for n, phase in product((3, 4, 5), range(2)):
        outcomes = Counter()
        example = None
        for books, left, right in survivors:
            loss, extra, witness = compare(*tile(books, left, right, n, phase))
            outcomes[loss, extra] += 1
            if witness and example is None:
                example = dict(training_books=books, left=left, right=right, excess=witness)
        rows.append(dict(sites=n, phase=phase, tested=len(survivors),
                         exact=outcomes.get((0, 0), 0), witness=example,
                         histogram=[dict(missing=k[0], extra=k[1], count=v)
                                    for k, v in sorted(outcomes.items())]))
    return rows


def window_obstruction(survivors):
    """Post-holdout control, not a search or a change to the frozen recipes.

    At any n>=4, two neighboring three-site windows would need to agree on
    their overlapping pair of books. Without such an overlap, a window has
    an extra raw path (never a missing native move by isolated exactness).
    Fix every exterior site at its own T code and every exterior helper at
    stock. The bad path still exists. The extra pair cannot become native:
    deleting the leftmost T sends aa<->bb to the same step, and Ta<->aT to
    itself or equality, according as that T is retained or deleted. Likewise
    for the rightmost T. Iterated deletion therefore retracts T^l u T^r to
    u throughout any putative native path between padded endpoints.

    This is an elementary argument for the isolated-exact template family,
    using the finite window census; the bounded deletion checks below are
    regression controls, not machine-checked universal proof artifacts.
    """
    books = sorted({b for b, _, _ in survivors})
    overlaps = [(a, b) for a in books for b in books if a[1:] == b[:2]]
    l3, l4 = native_labels(3), native_labels(4)
    nonnative = [(x, y) for x, y in combinations(words(3), 2) if l3[x] != l3[y]]
    collapses = {}
    for side, t in product(("left", "right"), "Tab"):
        def pad(w):
            return t+w if side == "left" else w+t
        collapses[side+"_"+t] = sum(l4[pad(x)] == l4[pad(y)] for x, y in nonnative)
    checks = violations = 0
    for n in range(2, 6):
        for x in words(n):
            if "T" not in x:
                continue
            for y in native_neighbors(x):
                for choose in (str.index, str.rindex):
                    ix, iy = choose(x, "T"), choose(y, "T")
                    a, b = x[:ix]+x[ix+1:], y[:iy]+y[iy+1:]
                    checks += 1
                    violations += a != b and b not in native_neighbors(a)
    return dict(overlapping_exact_book_windows=overlaps, nonnative_three_site_pairs=len(nonnative),
                spectator_collapses_3_to_4=collapses, erasure_step_checks_2_to_5=checks,
                erasure_violations=violations)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--recipes", action="store_true", help="include every exact three-site recipe")
    args = parser.parse_args()
    tr = training()
    hits = tr["survivors"]
    report = dict(book_order=BOOKS, triple_order=TRIPLES,
                  local_fits=[dict(books=k, count=len(v)) for k, v in tr["books_by_pair"].items()],
                  compatible_book_triples=tr["compatible_book_triples"],
                  fitted_recipe_pairs=tr["fitted_recipe_pairs"],
                  exact_three_sites=len(hits),
                  exact_by_books=[dict(books=b, count=v)
                                  for b, v in sorted(Counter(b for b, _, _ in hits).items())],
                  heldouts=heldouts(hits), window_obstruction=window_obstruction(hits))
    if args.recipes:
        report["recipes"] = hits
    print(json.dumps(report, sort_keys=True))


if __name__ == "__main__":
    main()
