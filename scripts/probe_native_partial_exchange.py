"""Co-located partial exchange of two *data* triangles, not their references.

Two actual reference stocks meet first; both corrected contact flags survive.
The data source, including the optional local preparation flag, precedes all
analyzer choices. Coherent splitting, lower-path winding, reunification,
signed cancellation, joint ordered-pair events and uniform seeds are supplied.
No numerical entangling angle, rotation or terminal probability is an input.
No independent finished-package sources, spacelike detector model or full QM.

With S the whole-data exchange and C the forward winding of reference A,
the first splitter sends a blank path to ((I+S)v,(I-S)v). Since C commutes
with S, the second splitter returns all amplitude to the blank port, as
2((I+S)v+C(I-S)v). After accounting for the gain 16 this is P+ + C P-.
On the balanced neutral references C_A=C_B and C^2+C+I=0, so one may
describe C as a common scalar omega (or its conjugate, by convention).
This diagnostic does not insert a complex number into the path rules.

Run: python3 -B -O -m scripts.probe_native_partial_exchange
"""

from collections import Counter, defaultdict
from fractions import Fraction as F
from functools import cache
from itertools import product

from scripts.probe_coherent_triangle_pulses import columns
from scripts.probe_prior_triangle_reference import (
    BITS,
    GRID,
    K,
    Stock,
    counts,
    edge,
    fast,
    fix_reference,
    gain,
    independent,
    index,
    move,
    need,
    norm,
    orbits,
    package_source,
    rank,
    read,
    routed,
    signed_vector,
)
from scripts.probe_triangle_exchange_source import median, route_block
from scripts.probe_triangle_reference_sewing import SWAP_CUR, dot, exchange, perm

W = len(GRID)
TURN = tuple(index(a, (r - 1) % 3, b, s) for a, r, b, s in GRID)  # pullback
TURN_B = tuple(index(a, r, b, (s - 1) % 3) for a, r, b, s in GRID)
ORTH = ((0, K), (2, 1))  # predicted Z,Y against two tilted trines
EDGES = ((1, 0), (K, 0))  # found by exploring the four native settings


def total(v, w):
    return tuple(x + y for x, y in zip(v, w, strict=True))


def scale(c, v):
    return tuple(c * x for x in v)


def check_operator():
    """Both splitter columns on every orbit; check all 81 blank-rail basis inputs."""

    def linear_split(v):
        out = [0] * (2 * W)
        for o in SWAP_ORBITS:
            ids = [W * p + i for p in BITS for i in o]
            for i, row in zip(ids, split_gate(len(o)), strict=True):
                out[i] = sum(a * v[j] for a, j in zip(row, ids, strict=True))
        return tuple(out)

    for i in range(W):
        basis = tuple(int(i == j) for j in range(W))
        up, lo = exchange(basis, SWAP_CUR)
        middle = linear_split(basis + (0,) * W)
        need(
            middle == up + lo and linear_split(middle) == scale(4, basis) + (0,) * W,
            "splitter blank-input columns or ray inverse",
        )
        turned = perm(middle[W:], TURN)
        need(
            linear_split(middle[:W] + turned) == scale(2, total(up, turned)) + (0,) * W,
            "entangler operator column",
        )


@cache
def split_gate(n):
    """Original path splitter on a one- or two-point whole-data-swap orbit."""

    def children(i):
        path, j = divmod(i, n)
        for p in BITS:
            yield n * p + j, 1
            yield n * p + n - 1 - j, 1 if p == path else -1

    return columns(2 * n, 2 * n, children)


SWAP_ORBITS = orbits(SWAP_CUR)
LOCATION = {r: (o, j) for o in SWAP_ORBITS for j, r in enumerate(o)}


@cache
def tiny_split(w):
    cloud = tuple(
        (i, 1 if x > 0 else -1) for i, x in enumerate(w) for _ in range(abs(x))
    )
    out, router, g, _ = route_block(cloud, split_gate(len(w) // 2))
    need(g == 4, "split gain")
    return out, router


def splitter(s):
    """Transport every ancestral ticket twice through the same splitter in pulse()."""
    groups = defaultdict(list)
    for ident, (rail, sign) in enumerate(s.cloud):
        hp, r = divmod(rail, W)
        h, p = divmod(hp, 2)
        o, j = LOCATION[r]
        groups[h, o].append((len(o) * p + j, ident, sign))
    cloud, seen, local = [], {}, {}
    for (h, o), entries in groups.items():
        w = [0] * (2 * len(o))
        for i, (j, ident, sign) in enumerate(sorted(entries)):
            seen[ident] = (h, o), i
            w[j] += sign
        need(sum(map(abs, w)) == len(entries), "uncancelled input")
        out, router = tiny_split(tuple(w))
        local[h, o] = len(cloud), router
        for j, z in out:
            p, r = divmod(j, len(o))
            cloud.append((W * (2 * h + p) + o[r], z))
    tickets = {}
    for t, (i, j) in s.tickets.items():
        key, a = seen[i]
        other, b = seen[j]
        need(key == other and s.cloud[i][0] == s.cloud[j][0], "split event locality")
        base, router = local[key]
        for seed in range(4):
            p, q = router[(a, b), seed]
            dest = base + p, base + q
            need(cloud[dest[0]][0] == cloud[dest[1]][0], "not a same-rail event")
            tickets[(*t, seed)] = dest
    rail = Counter(i for i, _ in cloud)
    need(
        len(tickets)
        == 4 * len(s.tickets)
        == len(set(tickets.values()))
        == sum(n * n for n in rail.values()),
        "split lost or aliased a ticket",
    )
    return Stock(tuple(cloud), tickets)


def relabel(s, f):
    distinct = {i for i, _ in s.cloud}
    need(len({f(i) for i in distinct}) == len(distinct), "relabel merged paths")
    return Stock(tuple((f(i), z) for i, z in s.cloud), s.tickets)


def pulse(s, policy):
    """Tagging records the middle path externally; neither tag is discarded."""
    s = relabel(s, lambda i: 2 * W * (i // W) + i % W)
    s = splitter(s)

    def middle(i):
        hp, r = divmod(i, W)
        h, p = divmod(hp, 2)
        a, u, b, v = GRID[r]
        shift = p if policy != "no turn" else 0
        if policy == "record":
            h = 2 * h + p
        return (2 * h + p) * W + index(a, (u + shift) % 3, b, v)

    out = splitter(relabel(s, middle))
    need(all(i // W % 2 == 0 for i, _ in out.cloud), "nonblank return path")
    return relabel(out, lambda i: W * (i // (2 * W)) + i % W)


def port_vectors(s, n):
    v = signed_vector(s, n * W)
    parts = tuple(v[i : i + W] for i in range(0, len(v), W))
    need(
        counts(s) == {i: norm(w) for i, w in enumerate(parts) if any(w)},
        "signed terminal multiplicity differs from addressed tickets",
    )
    return parts


def local_traces(v):
    # Actual package traces in the 9x9 real rail representation, not qubit marginals.
    rows = tuple(v[i : i + 9] for i in range(0, W, 9))
    mats = []
    for basis in (rows, tuple(zip(*rows, strict=True))):
        m = tuple(tuple(F(dot(x, y), norm(v)) for y in basis) for x in basis)
        need(sum(m[i][i] for i in range(9)) == 1, "trace normalization")
        mats.append((rank(m), sum(x * x for row in m for x in row)))
    return tuple(mats)


def terminal(v, k, l):
    """Each integer z denotes |z| surviving live addresses on that exact rail.

    Its complete ordered same-rail event stock has z*z members, self-pairs
    included. Different histories have separate live addresses. No terminal
    gate or comparison rescales the stock. Also replay in opposite order.
    """
    left, right = fast(v, 0, k), fast(v, 1, l)
    cells = []
    for a, b in product(BITS, repeat=2):
        z = fast(left[a], 1, l)[b]
        need(z == fast(right[b], 0, k)[a], "read order changed terminal signed paths")
        cells.append(norm(z))
    need(sum(cells) == norm(v) * gain(k) * gain(l), "missing terminal event")
    return tuple(cells)


def report(rows, settings):
    probs = {}
    corr = []
    for k, l in product(*settings):
        c = tuple(map(sum, zip(*(terminal(v, k, l) for v in rows), strict=True)))
        n = sum(c)
        p, q, r, s = (F(x, n) for x in c)
        probs[k, l] = p, p + q, p + r
        corr.append(p - q - r + s)
    for k in settings[0]:
        need(len({probs[k, l][1] for l in settings[1]}) == 1, "A signalling")
    for l in settings[1]:
        need(len({probs[k, l][2] for k in settings[0]}) == 1, "B signalling")
    return sum(corr[:3]) - corr[3], probs


def addressed_tables(s, src, settings):
    """Replay all choices and all terminal addresses, including every history."""
    # Process disjoint history blocks one at a time to bound memory. Only
    # carrier offsets change; every original ticket and its rail are preserved.
    for h, v in enumerate(src):
        ids = [i for i, (r, z) in enumerate(s.cloud) if r // W == h]
        position = {i: j for j, i in enumerate(ids)}
        block = Stock(
            tuple(s.cloud[i] for i in ids),
            {
                t: (position[i], position[j])
                for t, (i, j) in s.tickets.items()
                if i in position
            },
        )
        need(len(block.tickets) == norm(v), "wrong history stock")
        for k, l in product(*settings):
            found = counts(routed(routed(block, move(0, k)), move(1, l)))
            e = terminal(v, k, l)
            need(tuple(found[4 * h + j] for j in range(4)) == e, "addressed Bell table")
            need(
                sum(found.values()) == len(block.tickets) * gain(k) * gain(l),
                "wrong terminal ticket denominator",
            )


def microscopic(s):
    """A fixed ancestry and identical zero seeds, in two allowed B settings.

    The Bob seed alphabets have sizes 9 and 4. Zero is valid in both (e.g.
    the same zero draw in a common 36-element refinement). The ensembles
    themselves count every seed, including nonzero ones.
    """
    tracked = []
    src = port_vectors(s, 2)
    for l in EDGES[1]:
        first = routed(s, move(1, l))
        second = routed(first, move(0, EDGES[0][0]))
        all_exits = counts(second)
        for h in BITS:
            expected = terminal(src[h], EDGES[0][0], l)
            for a, b in product(BITS, repeat=2):
                need(
                    all_exits[(2 * h + b) * 2 + a] == expected[2 * a + b],
                    "addressed replay",
                )
        tracked.append(
            {
                t[:-2]: second.cloud[addr[0]][0] // W % 2
                for t, addr in second.tickets.items()
                if t[-2:] == (0, 0)
            }
        )
    need(tracked[0].keys() == tracked[1].keys(), "unstable source ancestry")
    flips = [t for t in tracked[0] if tracked[0][t] != tracked[1][t]]
    need(bool(flips), "no fixed-ticket remote-setting witness")
    return flips[0], tuple(m[flips[0]] for m in tracked)


def probe():
    check_operator()
    refs = fix_reference(read(independent(edge(0), edge(0)), K, 1))
    data = independent(edge(0), edge(0))
    # K means *no label shift* for package_source; neither setting here reads
    # a detector. The second data edge is cyclically relabelled to edge(1).
    raw = package_source(refs, data, K, 0)
    prepared = routed(raw, move(1, 0))
    need(
        counts(raw) == {0: 72, 1: 72}
        and counts(prepared) == {0: 216, 1: 72, 2: 216, 3: 72},
        "both reference branches and local 3:1 prep flags must survive",
    )
    policies = ("coherent", "record", "no turn")
    reference = signed_vector(refs, 18)
    for name, input_stock, histories, settings, scores in (
        ("raw edges", raw, 2, EDGES, ((F(33, 16), F(9, 8), F(3, 4)),)),
        ("local prep", prepared, 4, ORTH, ((F(5, 2), 1, 1), (-1, -1, -1))),
    ):
        start = port_vectors(input_stock, histories)
        for h, v in enumerate(start):
            ref_flag = h if histories == 2 else h // 2
            y = edge(1) if histories == 2 else (median(0), edge(0))[h % 2]
            input_ray = tuple(
                reference[9 * ref_flag + 3 * r + s] * edge(0)[a] * y[b]
                for a, r, b, s in GRID
            )
            need(
                v in (input_ray, scale(-1, input_ray)),
                "actual data/reference input ray",
            )
            cv = perm(v, TURN)
            need(
                cv == perm(v, TURN_B) and not any(total(total(v, cv), perm(cv, TURN))),
                "prior reference not balanced in a neutral winding sector",
            )
            need(local_traces(v) == ((2, F(1, 2)),) * 2, "initial real local trace")
        for p, policy in enumerate(policies):
            out = pulse(input_stock, policy)
            ntag = 2 if policy == "record" else 1
            branches = port_vectors(out, histories * ntag)
            addressed_tables(out, branches, settings)
            for h, v in enumerate(start):
                sym, anti = exchange(v, SWAP_CUR)
                lower = perm(anti, TURN) if policy != "no turn" else anti
                pieces = tuple(scale(2, z) for z in (sym, lower))
                expected = pieces if ntag == 2 else (total(*pieces),)
                rows = branches[h * ntag : (h + 1) * ntag]
                need(
                    rows == expected and sum(map(norm, rows)) == 16 * norm(v),
                    "split/turn/uncompute or history gain",
                )
                score, probs = report(rows, settings)
                b = h % 2 if histories == 4 else 0
                need(score == scores[b][p], "CHSH or retained control branch")
                if policy == "coherent":
                    diag = (
                        (4, F(101, 256))
                        if histories == 2
                        else ((4, F(5, 16)) if not b else (2, F(1, 2)))
                    )
                    need(
                        local_traces(rows[0]) == (diag,) * 2,
                        "real reduced package state",
                    )
                    if not b:
                        q, ma, mb = probs[settings[0][0], settings[1][0]]
                        need(q != ma * mb, "joint table factored on actual input flags")
                        if histories == 4:
                            need(
                                (q, ma, mb) == (F(9, 16), F(3, 4), F(5, 8)),
                                "orthogonal-input probability witness",
                            )
            unconditioned = report(branches, settings)[0]
            expected_all = (
                scores[0][p]
                if histories == 2
                else F(3 * scores[0][p] + scores[1][p], 4)
            )
            need(unconditioned == expected_all, "unconditioned CHSH")
            print(
                f"{name}; {policy}: per prior flag CHSH {', '.join(str(s[p]) for s in scores)}; "
                f"all branches {unconditioned}; {len(out.tickets)} source descendants"
            )
            if histories == 2 and policy == "coherent":
                print(
                    "B first, fixed source ticket and two zero seeds; A flip:",
                    microscopic(out),
                )
    print(
        "Raw local rank/purity on both sides: initially 2, 1/2 (shared reference); "
        "after coherent exchange: two raw edges 4, 101/256; orthogonal inputs 4, 5/16."
    )
    print(
        "Orthogonal-input CHSH 5/2 uses the 3/4 local B preparation flag; "
        "keeping both preparation flags gives 13/8. Raw-edge 33/16 needs no input herald."
    )
    print(
        "Each score includes both detector outputs per side. Prior reference, co-located "
        "source, coherent controls and joint event routing supplied; no spacelike mechanism."
    )


if __name__ == "__main__":
    probe()
