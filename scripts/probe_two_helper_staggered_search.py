"""Finite, unclocked two-private-helper census for alternating two-bit books.

The native pair generators are aa <-> bb and Ta <-> aT. Bits 0,1 encode the
left site; 2,3 the right; 4,5 are private to this edge. A recipe is (stock,
mask): the stock is required at both clean endpoints, never reset inside
a path. Bit j selects lexicographic triple j; any unanimous selected triple
can flip, in either direction, with unlimited intermediate dirty/noncode visits.
The experimental contract is equality of whole clean connectivity relations,
not raw path multiplicities, first-hit observations, times or local steps.

Search protocol: isolate both native moves, then independently check the whole
ABA and BAB graphs. Repeat the frozen recipes on whole n=4,5,6 paths of BOTH
phases. Only candidates passing both phases go on to the next size. First test
one template and its port reflection. Independent AB and BA are a second
family; do not quotient the two orientations as if they were the same move.
All claims here concern selected site codes and incidence, not their origin.

Run from root: python3 -m scripts.probe_two_helper_staggered_search
Add --mixed for the exhaustive independent-template existence test, or
--witness for compact replay of the selected recipe and its group invariant.
"""

import argparse
import json
from collections import Counter
from functools import cache
from hashlib import sha256
from itertools import combinations, combinations_with_replacement, product

from scripts import probe_staggered_binary_codebooks as prior

TRIPLES = tuple(combinations(range(6), 3))
ALL = tuple(range(len(TRIPLES)))
BOOK_PAIRS = tuple(
    p for p in product(range(len(prior.BOOKS)), repeat=2) if prior.compatible(*p)
)
STOCKS = (0, 1, 3)  # 10 maps to 01 by private wire exchange.
LINKS = tuple(
    tuple((x, x | m) for x in range(64) if not x & m)
    for m in (sum(1 << k for k in t) for t in TRIPLES)
)


def _root(ps, x):
    while ps[x] != x:
        x = ps[x]
    return x


@cache
def minima(books, stock, allowed=ALL):
    """All inclusion-minimal isolated-exact masks at these labeled local slots.

    Adding incidences only merges components, never removes a clean pair. Prune
    a branch at the first unlike clean colours in one raw class. At first exact
    agreement record its prefix and omit its supersets. A smaller exact mask
    may differ by an earlier exclusion, so remove recorded nonminima at the end.
    Consequently each exact mask contains a returned mask *at the same stock*.
    """
    clean = tuple(x | (stock << 4) for x in prior.codes(books))
    colour = [0] * 64
    labels = prior.native_labels(2)
    for x, w in zip(clean, prior.words(2)):
        colour[x] = 1 + labels[w]
    hits = []

    def dfs(j, mask, ps, cs):
        if _root(ps, clean[1]) == _root(ps, clean[3]) and _root(ps, clean[4]) == _root(
            ps, clean[8]
        ):
            hits.append(mask)
            return
        if j == len(allowed):
            return
        i = allowed[j]
        dfs(j + 1, mask, ps, cs)
        ps, cs = ps.copy(), cs.copy()
        changed = False
        for x, y in LINKS[i]:
            a, b = _root(ps, x), _root(ps, y)
            if a == b:
                continue
            if cs[a] and cs[b] and cs[a] != cs[b]:
                return
            changed = True
            ps[b] = a
            cs[a] = cs[a] or cs[b]
        if changed:  # otherwise this incidence is redundant in every extension
            dfs(j + 1, mask | (1 << i), ps, cs)

    dfs(0, 0, list(range(64)), colour)
    minimal = []
    for m in sorted(hits, key=int.bit_count):
        if not any(m & q == q for q in minimal):
            minimal.append(m)
    return tuple(sorted(minimal))


@cache
def _permute(mask, perm):
    return sum(
        1 << TRIPLES.index(tuple(sorted(perm[k] for k in t)))
        for j, t in enumerate(TRIPLES)
        if (mask >> j) & 1
    )


def mirror(mask):
    return _permute(mask, (2, 3, 0, 1, 4, 5))


def helper_canonical(recipe):
    s, m = recipe
    return min(recipe, ((s >> 1) | ((s & 1) << 1), _permute(m, (0, 1, 2, 3, 5, 4))))


@cache
def minimal_recipes(books):
    return tuple(
        sorted({helper_canonical((s, m)) for s in STOCKS for m in minima(books, s)})
    )


@cache
def _local_moves(n, edge, mask):
    slots = (*range(2 * edge, 2 * edge + 4), 2 * n + 2 * edge, 2 * n + 2 * edge + 1)
    return tuple(
        sum(1 << slots[k] for k in t) for j, t in enumerate(TRIPLES) if (mask >> j) & 1
    )


def compare(books, recipes):
    """Literal raw BFS; return missing/extra clean pairs and one excess witness."""
    n = len(books)
    if n < 2 or len(recipes) != n - 1:
        raise ValueError("one oriented edge recipe per neighboring pair required")
    moves = tuple(
        sorted(
            {m for e, (_, mask) in enumerate(recipes) for m in _local_moves(n, e, mask)}
        )
    )
    stock = sum(s << (2 * n + 2 * i) for i, (s, _) in enumerate(recipes))
    clean = {stock | x: w for x, w in zip(prior.codes(books), prior.words(n))}
    visited = bytearray(1 << (4 * n - 2))
    total = both = 0
    witness = None
    labels = prior.native_labels(n)
    for seed, first in clean.items():
        if visited[seed]:
            continue
        visited[seed] = 1
        queue, counts = [seed], Counter()
        for x in queue:
            w = clean.get(x)
            if w is not None:
                counts[labels[w]] += 1
                if witness is None and labels[first] != labels[w]:
                    witness = (first, w)
            for m in moves:
                if x & m in (0, m):
                    y = x ^ m
                    if not visited[y]:
                        visited[y] = 1
                        queue.append(y)
        total += prior.pairs_in(sum(counts.values()))
        both += sum(prior.pairs_in(v) for v in counts.values())
    native = sum(prior.pairs_in(len(g)) for g in prior.native_components(n))
    return native - both, total - both, witness


def tile(pair, ab, ba, n, phase):
    return (
        tuple(pair[(i + phase) % 2] for i in range(n)),
        tuple((ab, ba)[(i + phase) % 2] for i in range(n - 1)),
    )


@cache
def _window_moves(edge, mask):
    """Exact applicable XOR moves, indexed by the edge's six local bits."""
    local = _local_moves(2, 0, mask)
    global_masks = _local_moves(3, edge, mask)
    return tuple(
        tuple(g for m, g in zip(local, global_masks) if x & m in (0, m))
        for x in range(64)
    )


@cache
def _window_colours(books, s, t):
    stock = (s << 6) | (t << 8)
    clean = tuple(stock | x for x in prior.codes(books))
    colour = bytearray(1024)
    sizes = (0, *(len(c) for c in prior.native_components(3)))
    for x, w in zip(clean, prior.words(3)):
        colour[x] = 1 + prior.native_labels(3)[w]
    return clean, colour, sizes


def window_exact(books, recipes):
    """Three-site BFS with cached local moves and an early clean mismatch exit."""
    (s, a), (t, b) = recipes
    clean, colour, sizes = _window_colours(books, s, t)
    left, right = _window_moves(0, a), _window_moves(1, b)
    seen = bytearray(1024)
    for seed in clean:
        if seen[seed]:
            continue
        seen[seed] = 1
        ref, count = colour[seed], 0
        queue = [seed]
        for x in queue:
            if colour[x]:
                if colour[x] != ref:
                    return False
                count += 1
            for moves in (
                left[(x & 15) | ((x >> 2) & 48)],
                right[((x >> 2) & 15) | ((x >> 4) & 48)],
            ):
                for m in moves:
                    y = x ^ m
                    if not seen[y]:
                        seen[y] = 1
                        queue.append(y)
        if count != sizes[ref]:
            return False
    return True


def digest(value):
    return sha256(json.dumps(value, separators=(",", ":")).encode()).hexdigest()


def search_family(pair, mixed=False):
    """All minimal supports up to private names. Report orientation multiplicities.

    Store BA by its reflection into AB slots. Reflecting an entire palindrome
    window exchanges the two stored templates without changing its phase.
    Each off-diagonal pair thus represents two ordered choices. Whole chains
    of both phases are checked before reporting survival to a larger size.
    """
    recipes = minimal_recipes(pair)
    choices = (
        combinations_with_replacement(recipes, 2)
        if mixed
        else ((x, x) for x in recipes)
    )
    counts, hits = Counter(), []
    first = {}
    for ab, reflected_ba in choices:
        ba = reflected_ba[0], mirror(reflected_ba[1])
        weight = 1 if ab == reflected_ba else 2
        verdict = tuple(window_exact(*tile(pair, ab, ba, 3, p)) for p in range(2))
        counts[verdict] += weight
        if verdict not in first:
            first[verdict] = (ab, ba)
        if all(verdict):
            hits.append((ab, ba, weight))
    return recipes, counts, first, hits


def heldouts(pair, hits):
    rows = []
    for n in (4, 5, 6):
        both = []
        counts = Counter()
        example = {}
        for ab, ba, weight in hits:
            results = [compare(*tile(pair, ab, ba, n, phase)) for phase in range(2)]
            if any(missing for missing, _, _ in results):
                raise AssertionError("a local exact native generator failed to lift")
            verdict = tuple(extra == 0 for _, extra, _ in results)
            counts[verdict] += weight
            example.setdefault(verdict, {"ab": ab, "ba": ba, "comparisons": results})
            if all(verdict):
                both.append((ab, ba, weight))
        rows.append(
            {
                "sites": n,
                "checked_recipe_representatives": len(hits),
                "both_exact_ordered": counts[True, True],
                "both_survivor_sha256": digest(both),
                "examples": [
                    dict(phase_exact=v, **r) for v, r in sorted(example.items())
                ],
            }
        )
        hits = both
    return rows


# Post-search certificate for one frozen finite hit. No search values are
# needed by the raw BFS; none of these group elements is read by an E move.
SELECTED = ((3, 4), (0, 1026), (0, 393732))
A_WORDS = ("a", "T", "b", "Tab")
B_WORDS = ("a", "T", "bat", "b")
HELPER_WORDS = ("", "ba", "abat", "ta")
GENERATOR_PATHS = (
    {("aa", "bb"): (0, 14), ("Ta", "aT"): (1, 15, 4)},
    {("aa", "bb"): (0, 19, 63, 11), ("Ta", "aT"): (1, 53, 4)},
)


def normal(word):
    """Reduced syllables of (Z(T) x C2(a)) * C2(b); 't' is inverse of 'T'.

    This value classifies the *native* word components at a fixed word length.
    For clarity, the mathematical argument is separate from the finite replay:
    c=aa=bb is central in the native monoid (commutes with a, b and T). In a
    clean positive word move T past a, extract every aa or bb into a front
    stock of c, then repeat. More precisely, within each maximal {T,a}-block
    sort into T^i a^j and extract floor(j/2) copies of c. Merge consecutive
    b's into c; whenever blocks then meet, renormalize. Each extraction
    shortens the residual word by two. With no extraction remaining, the
    residual nonidentity alternating syllables are exactly the unique reduced
    word in the free product, with each T exponent nonnegative. Thus equal
    group values give identical residual words, and equal original lengths
    force equal counts of c. Re-expand c as aa to obtain native equivalence.
    Without fixed length this converse fails (aa and the empty word).
    """
    reduced = []
    for ch in word:
        if ch == "b":
            if reduced and reduced[-1] == "b":
                reduced.pop()
            else:
                reduced.append("b")
        elif ch in "Tta":
            i, j = reduced.pop() if reduced and reduced[-1] != "b" else (0, 0)
            i += (ch == "T") - (ch == "t")
            j ^= int(ch == "a")
            if i or j:
                reduced.append((i, j))
        else:
            raise ValueError("unknown group letter: " + ch)
    return tuple(reduced)


def invariant_links(helper_words=HELPER_WORDS):
    """Inspect every unordered raw link, not just links from clean seeds.

    The overall invariant is the ordered product of site values with K_h
    inserted between B and A on each active-helper bond. An AB flip fixes
    the outside factors; its clean/dirty site factors are contiguous. A BA
    flip touches just B K_h A. Ignore both inert AB helper bits. On clean
    endpoints all inserted factors are the identity and site factors are the
    actual native letters. Thus link preservation plus the fixed-length
    normal-form argument gives soundness on every open alternating path.
    Completeness lifts isolated native paths while the exterior stays idle.
    This is a pen-and-paper argument with a finite table check, not a Lean
    artifact, a derivation of the book/geometry, or a detector/clock model.
    """
    rows = []
    for phase, (_, m) in enumerate(SELECTED[1:]):
        left, right = (B_WORDS, A_WORDS) if phase else (A_WORDS, B_WORDS)
        size = 64 if phase else 16
        values = tuple(
            normal(
                left[x & 3]
                + (helper_words[x >> 4] if phase else "")
                + right[(x >> 2) & 3]
            )
            for x in range(size)
        )
        checked = failures = 0
        for j, triple in enumerate(TRIPLES):
            if not (m >> j) & 1:
                continue
            move = sum(1 << k for k in triple)
            for x in range(size):
                if not x & move:
                    checked += 1
                    failures += values[x] != values[x | move]
        rows.append((checked, failures))
    return tuple(rows)


def witness_report():
    return {
        "books": [prior.BOOKS[i] for i in SELECTED[0]],
        "recipes": SELECTED[1:],
        "local_clean_generator_paths": [
            {f"{u}->{v}": route for (u, v), route in paths.items()}
            for paths in GENERATOR_PATHS
        ],
        "triples": [
            [t for j, t in enumerate(TRIPLES) if (m >> j) & 1] for _, m in SELECTED[1:]
        ],
        "all_local_group_link_checks": invariant_links(),
        "group_labels_by_raw_slot_state": {
            "A": A_WORDS,
            "B": B_WORDS,
            "BA_private": HELPER_WORDS,
        },
        "complete_path_replays": [
            {
                "n": n,
                "phase": p,
                "missing_extra_witness": compare(*tile(*SELECTED, n, p)),
                "native_pairs": sum(
                    prior.pairs_in(len(g)) for g in prior.native_components(n)
                ),
            }
            for n in range(2, 7)
            for p in range(2)
        ],
    }


def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument(
        "--mixed", action="store_true", help="independent AB and BA minimal recipes"
    )
    p.add_argument(
        "--witness",
        action="store_true",
        help="only replay the selected finite hit and invariant",
    )
    p.add_argument(
        "--pair",
        nargs=2,
        type=int,
        help="target one residue-compatible ordered book pair",
    )
    args = p.parse_args()
    if args.witness:
        print(json.dumps(witness_report(), sort_keys=True))
        return
    pairs = [tuple(args.pair)] if args.pair else [b for b in BOOK_PAIRS if b[0] <= b[1]]
    if any(b not in BOOK_PAIRS for b in pairs):
        p.error("pair is not residue-compatible")
    for pair in pairs:
        recipes, counts, first, hits = search_family(pair, args.mixed)
        print(
            json.dumps(
                {
                    "books": pair,
                    "family": "independent" if args.mixed else "mirrored",
                    "canonical_isolated_minima": len(recipes),
                    "minima_sha256": digest(recipes),
                    "window_verdicts": [
                        {"phase_exact": v, "ordered": w, "example": first[v]}
                        for v, w in sorted(counts.items())
                    ],
                    "both_three_site_representatives": len(hits),
                    "both_sha256": digest(hits),
                    "heldouts": heldouts(pair, hits),
                },
                sort_keys=True,
            ),
            flush=True,
        )


if __name__ == "__main__":
    main()
