"""Three-packet exchange sectors from supplied unsigned four-rail sources.

Three orthogonal neutral Hadamard contrasts have connected bipartite path
witnesses. Their Cartesian product, ordered factor addresses, coherent copies
and signed cancellation, factor exchanges, three coherent cyclic paths, and
the complete ordered-pair/uniform-seed router are SUPPLIED. Four labels are
rails, not space dimensions. No sector is selected by nature in this probe.

Let C cycle factors and B=I+C+C^2. The two recorded preparation outputs are
E=Bv and X=(3I-B)v. E is an unsigned sum of three orthogonal permutation words,
not a standard-sector state. X is standard-sector. Both have zero mean for
each of the three pair swaps. Splitting E by I+T and I-T, retaining BOTH flags
incoherently, makes a genuinely balanced symmetric/antisymmetric mixture on
the SAME four-rail carrier. The cyclic classifier accepts that mixture surely
and X never. It has integer columns [B;3I-B] with Gram 9I, not a hand-entered
target probability. Every prior ticket and descendant seed is retained.

The indistinguishability is only of single pair-swap averages (and repeating
the same pair). Sequential DIFFERENT pair contacts distinguish the sources:
their two recorded bits agree with probability 1 for the mixture but 1/4 for
X. A three-cycle is thus a clean classifier, not a unique minimal witness.
On three neutral rails the local space has dimension two: its third exterior
power vanishes, so this antisymmetric three-factor source is unavailable.

Finite executable controls, not Lean proof, physical event/scale, exchange
statistics derivation, detector dynamics, general composites or QM closure.
Run: python3 -B -m scripts.probe_three_packet_exchange_sector
"""

from collections import Counter
from fractions import Fraction as F
from itertools import permutations, product

from scripts import probe_bipartite_triangle_origin as graph
from scripts.probe_cancellation_event_router import pairs, route_block
from scripts.probe_triangle_exchange_source import Stock, edge, initialize


def need(ok, why):
    if not ok:
        raise AssertionError(why)


CONTRASTS = ((1, 1, -1, -1), (1, -1, 1, -1), (1, -1, -1, 1))
POINTS = tuple(product(range(4), repeat=3))
POSITION = {x: i for i, x in enumerate(POINTS)}
N = len(POINTS)
SWAPS = ((1, 0, 2), (0, 2, 1), (2, 1, 0))
CYCLE = (1, 2, 0)


def permutation(p):
    return tuple(POSITION[tuple(x[i] for i in p)] for x in POINTS)


def permute(v, p):
    return tuple(v[j] for j in permutation(p))


def inner(v, w):
    return sum(a*b for a, b in zip(v, w, strict=True))


def signed(s):
    v = [0]*N
    for i, sign in s.cloud:
        v[i] += sign
    return tuple(v)


def stock(s):
    need(set(s.tickets.values()) == pairs(s.cloud), "incomplete live stock")
    return len(s.tickets)


def gate(kind):
    if isinstance(kind, int):
        p = permutation(SWAPS[kind])
        plus = tuple(tuple(int(i == j)+int(p[i] == j) for j in range(N)) for i in range(N))
        minus = tuple(tuple(int(i == j)-int(p[i] == j) for j in range(N)) for i in range(N))
    else:
        c, cc = permutation(CYCLE), permutation((2, 0, 1))
        plus = tuple(tuple(int(i == j)+int(c[i] == j)+int(cc[i] == j)
                           for j in range(N)) for i in range(N))
        minus = tuple(tuple(3*int(i == j)-plus[i][j] for j in range(N)) for i in range(N))
    return plus+minus


GATES = {k: gate(k) for k in (0, 1, 2, "cycle")}


def contact(s, kind, reverse=False):
    """Partition actual descendants by a flag; never reinitialize a branch."""
    cloud, router, gain, _ = route_block(s.cloud, GATES[kind], reverse)
    need(gain == (9 if kind == "cycle" else 4), "wrong seed gain")
    outputs = []
    for flag in (0, 1):
        old = [i for i, (rail, _) in enumerate(cloud) if rail//N == flag]
        pos = {i: j for j, i in enumerate(old)}
        emitted = tuple((cloud[i][0] % N, cloud[i][1]) for i in old)
        tickets = {}
        for t, pair in s.tickets.items():
            for seed in range(gain):
                a, b = router[pair, seed]
                need(cloud[a][0] == cloud[b][0], "cross-rail event")
                if a in pos:
                    tickets[(*t, seed)] = pos[a], pos[b]
        out = Stock(emitted, tickets)
        stock(out)
        outputs.append(out)
    need(sum(stock(s) for s in outputs) == gain*stock(s), "lost descendant or herald")
    return tuple(outputs)


def bins(source, kind, reverse=False):
    return tuple(sum(stock(contact(s, kind, reverse)[b]) for s in source) for b in (0, 1))


def unsigned_source():
    paths = []
    for v in CONTRASTS:
        plus = [i for i, x in enumerate(v) if x == 1]
        minus = [i for i, x in enumerate(v) if x == -1]
        tags = (plus[0], minus[0], plus[1], minus[1])
        g = graph.graph(tags, ((0, 1), (1, 2), (2, 3)))
        parity = graph.path_parity(g, 0)
        read = tuple(sum((1 if parity[u] == 0 else -1) for u, t in enumerate(g.tags) if t == i)
                     for i in range(4))
        need(read == v and graph.mass(g) == 4, "unsigned path witness")
        paths.append(g)
    raw = graph.independent(graph.independent(paths[0], paths[1]), paths[2])
    need(len(raw.tags) == 64 and graph.mass(raw) == 64, "unsigned Cartesian source")
    v = tuple(CONTRASTS[0][a]*CONTRASTS[1][b]*CONTRASTS[2][c] for a, b, c in POINTS)
    words = [permute(v, p) for p in permutations(range(3))]
    need(all(inner(a, b) == (64 if i == j else 0)
             for i, a in enumerate(words) for j, b in enumerate(words)), "orthogonal word orbit")
    return initialize(v)


def sequential(source, first, second):
    counts = Counter()
    for s in source:
        for a, child in enumerate(contact(s, first)):
            for b, out in enumerate(contact(child, second)):
                counts[a, b] += stock(out)
    total = sum(counts.values())
    return F(counts[0, 0]+counts[1, 1], total)


def three_rail_wall():
    points = tuple(product(range(3), repeat=3))
    xs = [edge(i) for i in range(3)]
    # Two basis edges span every neutral local triple. Trilinearity extends
    # the checked vanishing to all three-factor neutral inputs.
    for x, y, z in product(xs[:2], repeat=3):
        v = {p: x[p[0]]*y[p[1]]*z[p[2]] for p in points}
        anti = [sum((-1)**sum(p[i] > p[j] for i in range(3) for j in range(i+1, 3))
                    *v[tuple(q[i] for i in p)] for p in permutations(range(3))) for q in points]
        need(not any(anti), "three-rail antisymmetric control")


def main():
    src = unsigned_source()
    e, x = contact(src, "cycle")
    need((stock(e), stock(x)) == (192, 384), "recorded preparation denominators")
    # Keep both outputs and their independent actual event addresses: no
    # coherent recombination or fresh normalized sign-sector stock.
    mixture = contact(e, 0)
    need(tuple(map(stock, mixture)) == (384, 384), "balanced actual mixture")
    for b, s in enumerate(mixture):
        for p in SWAPS:
            need(permute(signed(s), p) == tuple((-1)**b*z for z in signed(s)), "sector label")
    for name, source in (("standard", (x,)), ("balanced mixture", mixture), ("unsigned E", (e,))):
        rates = []
        for k in range(3):
            n = bins(source, k)
            need(n[0] == n[1], "pair expectation is not zero")
            rates.append(F(n[0], sum(n)))
        cyc = bins(source, "cycle")
        expected = 0 if name == "standard" else 1
        need(F(cyc[0], sum(cyc)) == expected, "cycle classifier")
        need(bins(source, "cycle", True) == cyc, "matching changed classifier")
        need(sequential(source, 0, 0) == 1, "same-pair repeat")
        agree = sequential(source, 0, 1)
        need(agree == (F(1, 4) if name == "standard" else 1), "different-pair discriminator")
        print(f"{name}: input stock {sum(map(stock, source))}; pair plus {rates}; "
              f"cycle bins {cyc}; different-pair agreement {agree}.")
    three_rail_wall()
    print("Source stock64 -> cyclic heralds192/384; E -> retained swap flags384/384.")
    print("Unsigned E is NOT the standard sector; same pair averages do not fix sequential contacts.")
    print("Four neutral rails supplied; three-rail alternating sector absent. No physical sector selected.")


if __name__ == "__main__":
    main()
