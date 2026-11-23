"""Finite census of identical binary E-incidences on an open oriented path.

No clock, query, decoder action, or internal helper reset: reachability is
read between clean endpoint states in the complete unrestricted raw graph.
T,a,b are little-endian 00,10,01. The isolated native relations are exactly
aa~bb and Ta~aT. This does not demand deterministic paths or first-hit laws.

Mask bit j selects triple j (lexicographic combinations, or the displayed
restricted order). Stocks are little-endian helper integers. The restricted
two-data/one-helper family preserves Q=sum(data)-2*sum(helpers) exactly:
each flip changes these two sums by +/-2 and +/-1 with the same sign.
With all helpers returned, Q fixes the number of T's, but not the logical
connectivity within a T-count. No time, sampling law, or codebook is inferred.
Run: python3 -m scripts.probe_unclocked_template_census --full --mixed --recipes
"""

import argparse
from collections import Counter
from functools import lru_cache
from hashlib import sha256
from itertools import combinations, permutations, product
import json


def codebook_control():
    """All common injective site codes (T,a,b); residue or E-equivariant renaming.

    Clean helpers cancel in the raw Hamming-weight change aa->bb. Its residue
    forces equal singleton weights. Global complementation (including stocks)
    and/or within-site wire transposition normalize every survivor without
    changing the E move. This does not assume that local codewords stay valid
    during a move sequence, nor cover site-dependent encodings.
    """
    rows = []
    for t, a, b in permutations(range(4), 3):
        if 2*(a.bit_count() - b.bit_count()) % 3:
            rows.append(dict(code=(t, a, b), status="aa_bb_residue"))
        else:
            complement = t == 3
            swap = (a ^ (3 if complement else 0)) == 2
            rows.append(dict(code=(t, a, b), status="equivalent",
                             complement_all=complement, swap_data_wires=swap))
    return rows


def root(parents, x):
    while parents[x] != x:
        x = parents[x]
    return x


def local_fits(h, stock, edges):
    """All exact masks, including nonminimal and incidence-isomorphic ones.

    Each incidence adds every raw 000<->111 link on its three bits (other
    bits free). DFS branches exclude/include on each incidence. A raw
    component joining unlike desired logical classes can never split on
    adding more incidences, so and only so its branch is pruned. Check the
    two required equalities at a leaf, leaving the five singletons distinct.
    """
    n = 1 << (4 + h)
    initial = list(range(n))
    colour = [0]*n
    clean = {x+y: (stock << 4) + i + (j << 2) for i, x in enumerate("Tab")
             for j, y in enumerate("Tab")}
    groups = [("aa", "bb"), ("Ta", "aT"), ("TT",), ("ab",), ("ba",), ("Tb",), ("bT",)]
    for k, group in enumerate(groups, 1):
        for w in group:
            colour[clean[w]] = k
    links = []
    for triple in edges:
        mask = sum(1 << i for i in triple)
        links.append([(s, s | mask) for s in range(n) if not (s & mask)])
    hits = []

    def visit(j, chosen, parents, colours):
        if j == len(edges):
            if (root(parents, clean["aa"]) == root(parents, clean["bb"]) and
                    root(parents, clean["Ta"]) == root(parents, clean["aT"])):
                hits.append(chosen)
            return
        visit(j+1, chosen, parents, colours)
        ps, cs = parents.copy(), colours.copy()
        for x, y in links[j]:
            a, b = root(ps, x), root(ps, y)
            if a != b:
                if cs[a] and cs[b] and cs[a] != cs[b]:
                    return
                ps[b] = a
                cs[a] = cs[a] or cs[b]
        visit(j+1, chosen | (1 << j), ps, cs)

    visit(0, 0, initial, colour)
    return sorted(hits)


@lru_cache(maxsize=None)
def native_pairs(sites):
    """Ternary reference BFS, without using the binary representation."""
    words = set(map("".join, product("Tab", repeat=sites)))
    swap = {"aa": "bb", "bb": "aa", "Ta": "aT", "aT": "Ta"}
    pairs = set()
    while words:
        first = words.pop()
        queue, component = [first], [first]
        while queue:
            x = queue.pop()
            for i in range(sites-1):
                pair = x[i:i+2]
                if pair not in swap:
                    continue
                y = x[:i] + swap[pair] + x[i+2:]
                if y in words:
                    words.remove(y)
                    queue.append(y)
                    component.append(y)
        pairs.update(combinations(sorted(component), 2))
    return frozenset(pairs)


def clean_pairs(h, stock, edges, mask, sites):
    """Independent raw BFS, with no union-find, class colours or pruning."""
    recipe = (h, stock, tuple(triple for j, triple in enumerate(edges) if mask >> j & 1))
    return mixed_pairs((recipe,)*(sites-1))


def mixed_pairs(recipes):
    """Unrestricted reachability for an ordered list of individual recipes."""
    sites = len(recipes) + 1
    moves = set()
    helper_bits = 0
    priv = 2*sites
    for i, (h, stock, chosen) in enumerate(recipes):
        helper_bits |= stock << priv
        slots = [2*i+j for j in range(4)] + list(range(priv, priv+h))
        priv += h
        for triple in chosen:
            moves.add(sum(1 << slots[k] for k in triple))
    code = {helper_bits | sum("Tab".index(x) << (2*j) for j, x in enumerate(w)): "".join(w)
            for w in product("Tab", repeat=sites)}
    unseen = set(code)
    pairs = set()
    while unseen:
        first = unseen.pop()
        seen, component, queue = {first}, [code[first]], [first]
        while queue:
            x = queue.pop()
            for move in moves:
                if x & move not in (0, move):
                    continue
                y = x ^ move
                if y not in seen:
                    seen.add(y)
                    queue.append(y)
                    if y in unseen:
                        unseen.remove(y)
                        component.append(code[y])
        pairs.update(combinations(sorted(component), 2))
    return pairs


TWO = tuple(combinations(range(6), 3))


def two_recipe(stock, mask):
    return (2, stock, tuple(t for j, t in enumerate(TWO) if mask >> j & 1))


def swap_helpers(stock, mask):
    """Private relabeling 4<->5, fixing all four data bits and both port roles."""
    remap = (0, 1, 2, 3, 5, 4)
    changed = sum(1 << TWO.index(tuple(sorted(remap[k] for k in t)))
                  for j, t in enumerate(TWO) if mask >> j & 1)
    return (stock >> 1 | ((stock & 1) << 1)), changed


def minimal_templates():
    """Stock-specific minimal masks; every exact mask contains one such mask."""
    minimal = []
    for stock in range(4):
        row = []
        for m in sorted(local_fits(2, stock, TWO), key=int.bit_count):
            if not any(m & q == q for q in row):
                row.append(m)
        minimal.extend((stock, m) for m in row)
    return sorted(minimal)


def mixed_census():
    """All ordered minimal pairs, modulo only independent private helper names.

    All masks are considered in both data-port roles (no port quotient).
    Width 0 or 1 embeds at width 2 with unused private bits. For a no-go,
    an unwanted pair found for each ordered pair of minimal supports survives
    any enlargement to isolated-exact supports. The histogram counts labeled
    *minimal* pairs, not all their supersets. No general compiler no-go follows.
    """
    minimal = minimal_templates()
    reps = Counter(min(key, swap_helpers(*key)) for key in minimal)
    if any(swap_helpers(*key) not in minimal for key in minimal):
        raise AssertionError("private helper relabeling must give an exact minimal mask")
    recipes = {x: two_recipe(*x) for x in reps}
    native = native_pairs(3)
    survivors = []
    hist = Counter()
    best = None
    nearest = []
    for x, a in recipes.items():
        for y, b in recipes.items():
            raw = mixed_pairs((a, b))
            if native - raw:
                raise AssertionError("isolated path lift failed")
            extra = len(raw - native)
            hist[extra] += reps[x]*reps[y]
            if not extra:
                survivors.append((x, y))
            if best is None or extra < best:
                best, nearest = extra, []
            if extra == best:
                nearest.append(dict(left=x, right=y, multiplicity=reps[x]*reps[y],
                                    extra_pairs=sorted(raw-native)))
    return dict(minimal_labeled=len(minimal), minimal_representatives=len(reps),
                representative_pairs=len(reps)**2, labeled_pairs=len(minimal)**2,
                survivors=survivors, nearest_minimal_representatives=nearest,
                labeled_extra_histogram=dict(sorted(hist.items())))


def compare_path(h, stock, edges, mask, sites):
    raw = clean_pairs(h, stock, edges, mask, sites)
    native = native_pairs(sites)
    return len(native - raw), len(raw - native)


def census(h, stock, edges, recipes=False):
    fits = local_fits(h, stock, edges)
    hist = Counter()
    survivors = []
    for m in fits:
        loss, extra = compare_path(h, stock, edges, m, 3)
        if loss:
            raise AssertionError("each isolated native path lifts with neighbors idle")
        hist[extra] += 1
        if not extra:
            survivors.append(m)
    four = {m: compare_path(h, stock, edges, m, 4) for m in survivors}
    row = dict(helpers=h, stock=stock, edges=edges, template_count=1 << len(edges),
               isolated_fits=len(fits), fit_sha256=sha256(json.dumps(fits).encode()).hexdigest(),
               three_site_extra_histogram=dict(sorted(hist.items())),
               three_site_survivors=survivors, four_site_loss_extra=four)
    if recipes:
        row["all_isolated_masks"] = fits
    return row


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--full", action="store_true", help="include unrestricted two-helper census")
    parser.add_argument("--recipes", action="store_true", help="emit every labeled isolated-fit mask")
    parser.add_argument("--mixed", action="store_true", help="also try ordered heterogeneous minimal pairs")
    args = parser.parse_args()
    print(json.dumps(dict(uniform_codebooks=codebook_control()), sort_keys=True), flush=True)
    for h, edges in [(1, tuple(combinations(range(5), 3))),
                     (2, tuple((i, j, k) for i, j in combinations(range(4), 2) for k in (4, 5))),
                     *([(2, tuple(combinations(range(6), 3)))] if args.full else [])]:
        for stock in range(1 << h):
            print(json.dumps(census(h, stock, edges, args.recipes), sort_keys=True), flush=True)
    if args.mixed:
        print(json.dumps(mixed_census(), sort_keys=True))


if __name__ == "__main__":
    main()
