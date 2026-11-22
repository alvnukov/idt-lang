"""When do local rail names leave a detectable loop comparison?

Assume a connected graph, coherent path alternatives, and lossless additive
integer transport preserving an oriented quarter-turn J on the two signed
rails. The integer orthogonal matrices have signed unit columns, so comprise
eight signed permutations; exactly four commute with J, namely its powers.
No local-label argument supplies the graph, its edge transports, propagation,
or a nonzero loop phase. Mere frame differences give identity on ALL loops.

Write a link as the exponent a of J^a; reverse traversal has exponent -a.
Renaming the frame at v by J^g(v) changes a(u,v) by g(v)-g(u). Along
an open path only endpoint terms survive, so the difference of two path
phases with common endpoints is invariant. On a tree all links can be
removed. In a connected graph, fixing the root frame sets all tree links
to zero uniquely; the remaining edges record independent cycles.

On a 2x2 periodic square complex each positive edge is a separate cell:
the two positive x edges in one row are NOT oppositely traversed copies
of one edge. We exhaust the finite fields, classifying by four oriented
plaquette sums (one redundant) and the two fundamental periods.

The four-physical-port simulation is an explicit *supplied* detector
model: native balanced mixer T, coherent port shutter, grouped squared
norms. A herald prepares (z,-z) on one logical rail pair, with half the
injections rejected. T on that pair is exactly J on its logical value.
Parallel T across corresponding physical ports is a balanced splitter
of two logical arms, and its cube is its inverse. Link phases here are
compiled controlled elements on paths, not a discovered spatial field.
An incoherent arm record, absolute one-path intensity, or conjugating the
entire apparatus is a countercontrol. No continuous U(1), Maxwell law,
physical charges, gauge dynamics, or experimental confirmation follows.

Run: python3 -O -m scripts.probe_phase_comparison_links
"""

from collections import Counter
from fractions import Fraction as F
from itertools import permutations, product

Field = tuple[int, ...]
Gauge = tuple[int, ...]
Signature = tuple[int, int, int, int, int, int]
Vec = tuple[int, int]
Layer = tuple[tuple[int, int], ...]


def need(test: bool, reason: str) -> None:
    if not test:
        raise ValueError(reason)


def turn(v: Vec) -> Vec:
    return -v[1], v[0]


def classify_frames() -> None:
    e: tuple[Vec, Vec] = ((1, 0), (0, 1))
    oriented = set()
    for (a, b), (s, t) in product(permutations(e), product((1, -1), repeat=2)):
        first, second = (a[0] * s, a[1] * s), (b[0] * t, b[1] * t)
        if turn(first) == second:
            oriented.add((first, second))
    powers = set()
    first, second = e
    for _ in range(4):
        powers.add((first, second))
        first, second = turn(first), turn(second)
    need(oriented == powers and len(powers) == 4, "integer oriented isometries")


def reframe(a: Field, g: Gauge) -> Field:
    return tuple(
        (a[2 * v + axis] + g[v ^ (1 << axis)] - g[v]) % 4
        for v in range(4)
        for axis in range(2)
    )


def canonical(a: Field) -> Field:
    # Root 0; tree: 0->1 (x), 0->2 (y), 1->3 (y).
    return reframe(a, (0, -a[0], -a[1], -a[0] - a[3]))


def signature(a: Field) -> Signature:
    def face(v: int) -> int:
        return (a[2 * v] + a[2 * (v ^ 1) + 1] - a[2 * (v ^ 2)] - a[2 * v + 1]) % 4

    return (face(0), face(1), face(2), face(3), (a[0] + a[2]) % 4, (a[1] + a[5]) % 4)


def torus() -> None:
    reps: dict[Signature, Field] = {}
    count: Counter[Signature] = Counter()
    for a in product(range(4), repeat=8):
        sig, rep = signature(a), canonical(a)
        need(sum(sig[:4]) % 4 == 0 and signature(rep) == sig, "gauge invariants")
        need(rep[0] == rep[1] == rep[3] == 0, "tree frame")
        need(reps.setdefault(sig, rep) == rep, "signature identifies orbit")
        count[sig] += 1
    flat = {s for s in reps if s[:4] == (0, 0, 0, 0)}
    need(len(reps) == 1024 and set(count.values()) == {64}, "orbits")
    need({s[4:] for s in flat} == set(product(range(4), repeat=2)), "flat sectors")
    zero = (0,) * 8
    twist = (0, 0, 1, 0, 0, 0, 1, 0)
    need(signature(twist) == (0, 0, 0, 0, 1, 0), "flat x twist")
    for g in product(range(4), repeat=4):
        need(canonical(reframe(zero, g)) == zero, "pure-gauge control")
        b = reframe(twist, g)
        # Two x links wind once, two y links wind once, same endpoints.
        h = (b[0] + b[2] - b[1] - b[5]) % 4
        need(h == 1 and canonical(b) == canonical(twist), "twist vs pure labels")
        # Open alternatives 0->1->3 and 0->2->3: individual path coordinates
        # need not be invariant, but both acquire the same endpoint offset.
        for u, v in ((0, 3), (1, 4)):
            need(
                (b[u] + b[v] - twist[u] - twist[v] - g[3] + g[0]) % 4 == 0,
                "open-path covariance",
            )
    print("2x2 torus: 65536 assignments, 1024 gauge classes, 16 flat sectors;")
    print("  64 pure frame-difference assignments; flat x twist=1 is not among them.")


def layer(
    v: tuple[Vec, ...], pairs: Layer, conjugated: bool = False
) -> tuple[Vec, ...]:
    """Integer numerators; one shared factor of two in the denominator."""
    kappa = -1 if conjugated else 1
    v = tuple((a, kappa * b) for a, b in v)
    out = [(2 * x, 2 * y) for x, y in v]
    for j, k in pairs:
        (a, b), (c, d) = v[j], v[k]
        out[j] = (a - b + c + d, a + b - c + d)
        out[k] = (a + b + c - d, -a + b + c + d)
    return tuple((a, kappa * b) for a, b in out)


def intensities(
    left: int, right: int, *, flagged: bool = False, conjugated: bool = False
) -> tuple[F, F, F]:
    """Raw per injection: return, other port group, rejected source."""
    v: tuple[Vec, ...] = ((1, 0), (0, 0), (0, 0), (0, 0))
    v = layer(layer(v, ((0, 1),), conjugated), ((0, 2), (1, 3)), conjugated)
    m = -2 if conjugated else 2
    need(v == ((0, m), (2, 0), (2, 0), (0, -m)), "heralded preparation")
    v = (v[0], (0, 0), (0, 0), v[3])
    divisor = 8
    split = ((0, 1), (3, 2))
    v = layer(v, split, conjugated)
    # Orthogonal path flags: track branch amplitudes separately and add
    # intensities, so there is no unearned coherence at recombination.
    branches = (
        [v]
        if not flagged
        else [(v[0], (0, 0), (0, 0), v[3]), ((0, 0), v[1], v[2], (0, 0))]
    )
    word = [((0, 3),)] * (left % 4) + [((1, 2),)] * (right % 4) + [split] * 3
    for gates in word:
        branches = [layer(w, gates, conjugated) for w in branches]
        divisor *= 2

    def weight(ports: tuple[int, int]) -> F:
        return F(sum(x * x for w in branches for p in ports for x in w[p]), divisor**2)

    return weight((0, 3)), weight((1, 2)), F(1, 2)


def fringe() -> None:
    unshifted: dict[int, F] = {}
    oriented: dict[int, tuple[F, F]] = {}
    cos = (1, 0, -1, 0)
    for a, b in product(range(4), repeat=2):
        h = (a - b) % 4
        settings = []
        for r in (0, 1):
            p, q, reject = intensities(a + r, b)
            need(p + q + reject == 1, "track failures")
            target = F(1 + cos[(h + r) % 4], 2)
            need(p * 2 == target, "native return per herald")
            need(
                intensities(a + r, b, conjugated=True) == (p, q, reject),
                "conjugate apparatus",
            )
            need(intensities(-a - r, -b) == (p, q, reject), "reverse arms AND bias")
            need(
                intensities(a + r, b, flagged=True) == (F(1, 4), F(1, 4), F(1, 2)),
                "which-path flag",
            )
            settings.append(target)
        unshifted[h] = settings[0]
        oriented[h] = (settings[0], settings[1])
    need(unshifted[1] == unshifted[3], "single reference cannot orient")
    need(len(set(oriented.values())) == 4, "two references distinguish all C4 values")
    print("return per herald at references 0,+1, for h=0,1,2,3:")
    print(" ", ", ".join(f"({p}, {q})" for p, q in (oriented[h] for h in range(4))))
    print("per injection: multiply by 1/2; source failure 1/2 in every setting.")
    print(
        "which-path flag: 1/2 per herald. Conjugating arms AND analyzer preserves rates."
    )


def run() -> None:
    classify_frames()
    torus()
    fringe()


if __name__ == "__main__":
    run()
