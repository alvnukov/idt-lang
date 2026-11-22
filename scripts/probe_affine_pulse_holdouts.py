"""Same-source, same-detector census of native order-six ternary pulse maps.

Three active cells carry F5 labels; a fourth background reference is fixed
at zero. Primitive contacts L (cells 01), R (12) are (a,b)->(4a+2b,2a+4b).
A is the *whole* pulse LRLR in chronological order. Four equally weighted
histories start at s, As, As, A²s. The single frozen terminal detector is
bright if the FIRST wire is at background now OR after one inverse A. It
is never visited between pulse letters. This center-defect s=(0,1,0)
candidate was chosen after a failed end-defect/two-delayed-visit candidate;
that rejected apparatus is checked below rather than renamed a prediction.

All order-six maps are screened before mixed words; native means generated
by the two fixed contacts. A candidate B may use any finite contact word,
not necessarily the same length as A. Lowercase is the inverse of the
entire pulse. Existing rotation-comparison protocols are frozen in
probe_phase_pair_holdout.py: q=P(Ab) alone calibrates the supplied family;
q=1/2 and 3/4 have discriminating second holdouts. ABBB a is a separate
quadrature-calibration word (target 3/4); ABab is the group commutator
in the stated left-to-right convention, NOT that calibration.

Algebraic explanation: contacts preserve the common mean and are linear
on the 2-D deviation plane. The enumerated action is all GL2(5). An
order-six matrix has minimal polynomial X²-X+1: the field has no scalar
of order three, and X^6-1 is separable. Thus B³=-I for every such B;
all belong to one conjugacy class with centralizer F25* of order 24.
As -I is central, ABBB a is just B³ for every candidate, before the solo
filter. The readout here never reaches the separate quadrature calibration.
The complete six-count solo requirement rejects every noncommuting candidate
before an interior q may be assigned. This is not a failed mixed prediction
at a calibration that was reached. No claim about other stocks, detectors,
gate groups, larger periods hiding a six-step observable, or physics.

Run: python3 -B -O -m scripts.probe_affine_pulse_holdouts
"""

from collections import Counter
from itertools import product

Perm = tuple[int, ...]
Triple = tuple[int, int, int]
TAGS: tuple[Triple, ...] = tuple(product(range(5), range(5), range(5)))
IDENT: Perm = tuple(range(125))
FRINGE = (4, 3, 1, 0, 1, 3)
WORDS = ("Ab", "AB", "ABAB", "ABBBa", "ABab")


def need(ok: bool, why: str) -> None:
    if not ok:
        raise ValueError(why)


def encode(x: int, y: int, z: int) -> int:
    return 25 * x + 5 * y + z


def contacts() -> tuple[Perm, Perm]:
    left = tuple(
        encode((4 * x + 2 * y) % 5, (2 * x + 4 * y) % 5, z) for x, y, z in TAGS
    )
    right = tuple(
        encode(x, (4 * y + 2 * z) % 5, (2 * y + 4 * z) % 5) for x, y, z in TAGS
    )
    need(tuple(sorted(left)) == tuple(sorted(right)) == IDENT, "primitive permutations")
    return left, right


def then(p: Perm, q: Perm) -> Perm:
    """First p, then q."""
    return tuple(q[j] for j in p)


def power(p: Perm, n: int) -> Perm:
    g = IDENT
    for _ in range(n):
        g = then(g, p)
    return g


def gates() -> tuple[Perm, list[Perm]]:
    left, right = contacts()
    maps = [IDENT]
    seen = {IDENT}
    for g in maps:
        for h in (left, right):
            p = then(g, h)
            if p not in seen:
                seen.add(p)
                maps.append(p)
    return power(then(left, right), 2), maps


def plane_matrix(g: Perm) -> tuple[int, int, int, int]:
    # Columns in deviation coordinates (x-mean,y-mean); z-mean is minus their sum.
    a, c, _ = TAGS[g[encode(1, 0, 4)]]
    b, d, _ = TAGS[g[encode(0, 1, 4)]]
    for i, (x, y, z) in enumerate(TAGS):
        mean = 2 * (x + y + z) % 5
        u, v = x - mean, y - mean
        u1, v1 = a * u + b * v, c * u + d * v
        need(
            g[i] == encode((mean + u1) % 5, (mean + v1) % 5, (mean - u1 - v1) % 5),
            "deviation action",
        )
    return a, b, c, d


def measure(stock: Perm, bright: frozenset[int], g: Perm) -> int:
    return sum(g[i] in bright for i in stock)


def main() -> None:
    a, group = gates()
    matrices = {plane_matrix(g) for g in group}
    gl = {
        (u, v, w, x)
        for u, v, w, x in product(range(5), repeat=4)
        if (u * x - v * w) % 5
    }
    need(matrices == gl and len(group) == len(gl) == 480, "full native GL2(5)")
    six = [
        g
        for g in group
        if power(g, 6) == IDENT and power(g, 2) != IDENT and power(g, 3) != IDENT
    ]
    need(len(six) == 20 and a in six, "order-six census")
    need(
        all(plane_matrix(power(g, 3)) == (4, 0, 0, 4) for g in six),
        "common central cube",
    )
    need(len({g for g in group if then(a, g) == then(g, a)}) == 24, "centralizer size")
    ai = power(a, 5)
    old_seed, seed = encode(1, 0, 0), encode(0, 1, 0)
    old = (old_seed, a[old_seed], a[old_seed], a[a[old_seed]])
    stock = (seed, a[seed], a[seed], a[a[seed]])
    old_detector = frozenset(
        i for i in IDENT if TAGS[ai[i]][2] == 0 or TAGS[ai[ai[i]]][2] == 0
    )
    detector = frozenset(i for i in IDENT if TAGS[i][0] == 0 or TAGS[ai[i]][0] == 0)
    need(
        tuple(measure(old, old_detector, power(a, n)) for n in range(6))
        == (3, 3, 1, 0, 0, 1),
        "rejected two-delayed-visit fixture changed",
    )
    # Freeze the entire solo screen before evaluating even the diagnostic mixed words.
    solos = {
        b: tuple(measure(stock, detector, power(b, n)) for n in range(6)) for b in six
    }
    prefix = [b for b in six if solos[b][:4] == FRINGE[:4]]
    survivors = {b for b in six if solos[b] == FRINGE}
    need(len(prefix) == 4 and survivors == {a, ai}, "truncated-vs-complete solo census")
    need(
        len([b for b in six if then(a, b) != then(b, a)]) == 18,
        "noncommuting stock alternatives",
    )
    need(
        all(solos[b] == (4, 3, 1, 0, 2, 0) for b in prefix if b not in survivors),
        "prefix countercontrols",
    )
    mixed_all: dict[Perm, tuple[int, ...]] = {}
    for b in six:
        commands = {"A": a, "a": ai, "B": b, "b": power(b, 5)}
        row = []
        for word in WORDS:
            g = IDENT
            for letter in word:
                g = then(g, commands[letter])
            if word == "ABBBa":
                need(g == power(a, 3), "common conjugate half turn")
            row.append(measure(stock, detector, g))
        mixed_all[b] = tuple(row)
    rows = {b: mixed_all[b] for b in survivors}
    need(
        rows == {a: (4, 1, 1, 0, 4), ai: (1, 4, 4, 0, 4)},
        "mixed rows for the exact survivors",
    )
    impostors = sorted((plane_matrix(b), mixed_all[b]) for b in prefix if b not in rows)
    all_q = Counter(row[0] for row in mixed_all.values())
    need(all_q == {0: 4, 1: 6, 2: 5, 3: 4, 4: 1}, "uncalibrated candidate counts")
    misleading = [
        b for b, r in mixed_all.items() if r[0] in (2, 3) and r[0] + r[1] == 5
    ]
    need(
        len(misleading) == 2
        and all(solos[b] == (4, 2, 3, 0, 3, 2) for b in misleading)
        and {mixed_all[b][:3] for b in misleading} == {(2, 3, 0), (3, 2, 4)},
        "unscreened interior/first-holdout matching is not joint calibration",
    )
    print("Rejected delayed-end detector on end defect: 3,3,1,0,0,1 (not the target).")
    print(
        "Corrected center defect, first wire now/after inverse: 480 native maps; 20 order six."
    )
    print(
        "Only A and inverse A retain all six solo counts; 0/18 noncommuting maps survive."
    )
    print("Counts/4 for (Ab,AB,ABAB,ABBBa,ABab):", rows[a], rows[ai])
    print(
        "Neither interior q nor separate quadrature calibration reached after solo screening."
    )
    print(
        "Stopping at n=3 admits two extra maps: (deviation matrix, mixed counts)",
        impostors,
    )
    print(
        "Unscreened q counts (out of four) and frequencies, not calibrated survivors:",
        sorted(all_q.items()),
    )
    print(
        "Skipping solos gives two apparent interior q/first-holdout hits; both have solo 4,2,3,0,3,2."
    )


if __name__ == "__main__":
    main()
