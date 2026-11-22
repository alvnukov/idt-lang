"""Can an affine common reset hide outside the six F5 preparation codes?

Keep background zero, the center-seed orbit, four fair tickets at phases
k,k+1,k+1,k+2, the recorded first D bit, and all 480 native D-after-word
analyzers fixed. Ask for the conditional *statistics* of preparation P0
(bright) or P3 (dark) after each Pk; do not assume raw code membership.
P0 and P3 here are named preparations, not extremal raw distributions.

The final measurement ignores common nonzero color rescaling. Its 240
distinct effects plus normalization leave two more linear ambiguities on
the 32 resulting classes. Nevertheless positivity pins the masses of these
two target stocks on their three rays. An affine map of the input plane
to arbitrary F5 triples can leave the six-code plane while preserving
these supports, but every surviving ray action permutes the three bright
labels. A common mixture of permutations cannot reset each input to 1:2:1.

This grants independent randomness over arbitrary affine maps (more than
a fixed color circuit with independent ancillas). It excludes neither
outcome- or state-dependent control, pre-correlated preparations, a new
color gate, a different reader, nor general measurement instruments.
Finite executable result; no experimental uncertainty, quantum-state
certification or universal physical no-go. Run with or without -O:
python3 -B -m scripts.probe_affine_projective_reset
"""

from __future__ import annotations

from collections import Counter, defaultdict
from itertools import permutations, product

from scripts.probe_affine_contact_fringe import Six, cycle, detector, need
from scripts.probe_affine_pulse_holdouts import IDENT, TAGS, Triple, encode, gates

Row = tuple[int, ...]
Basis = tuple[Triple, Triple, Triple]
ORIGIN: Triple = (0, 0, 0)
CONSTANT: Triple = (1, 1, 1)


def scale(s: Triple, k: int) -> Triple:
    return k * s[0] % 5, k * s[1] % 5, k * s[2] % 5


def ray(s: Triple) -> Triple:
    first = next((x for x in s if x), 1)
    return scale(s, pow(first, -1, 5))


def lower_rank(rows: list[Row]) -> int:
    """A nonzero minor mod 101 is a nonzero integer minor over Q/R."""
    basis: dict[int, Row] = {}
    for row in rows:
        v = list(row)
        for j, b in sorted(basis.items()):
            k = v[j] % 101
            if k:
                v = [(x - k * y) % 101 for x, y in zip(v, b, strict=True)]
        j = next((i for i, k in enumerate(v) if k % 101), len(v))
        if j < len(v):
            inv = pow(v[j], -1, 101)
            basis[j] = tuple(k * inv % 101 for k in v)
    return len(basis)


def dot(a: Row, b: Row) -> int:
    return sum(x * y for x, y in zip(a, b, strict=True))


def class_group(r: Triple) -> int:
    if r == ORIGIN:
        return 0
    if r == CONSTANT:
        return 1
    return 2 if sum(r) % 5 == 0 else 3


def tomography(orbit: tuple[Triple, ...]) -> None:
    rays = tuple(sorted({ray(s) for s in TAGS}))
    sizes = Counter(ray(s) for s in TAGS)
    need(
        sizes[ORIGIN] == 1 and all(sizes[r] == 4 for r in rays if r != ORIGIN),
        "raw fibers",
    )
    kinds = tuple(class_group(r) for r in rays)
    need(Counter(kinds) == {0: 1, 1: 1, 2: 6, 3: 24}, "ray classes")
    d = {i for i, s in enumerate(TAGS) if detector(s, 0)}
    _, group = gates()
    effects: set[Row] = set()
    for g in group:
        need(
            all((g[i] in d) == (g[encode(*ray(TAGS[i]))] in d) for i in IDENT),
            "analyzer not ray invariant",
        )
        effects.add(tuple(int(g[encode(*r)] in d) for r in rays))
    rows = sorted(effects)
    normalized = [*rows, (1,) * len(rays)]
    need(len(group) == 480 and len(rows) == 240, "analyzer orbit")
    need(lower_rank(rows) == 29 and lower_rank(normalized) == 30, "modular lower ranks")
    directions = ((-2, -4, 1, 0), (-9, -15, 0, 1))
    k0, k1 = (tuple(v[c] for c in kinds) for v in directions)
    diag = tuple(int(r == CONSTANT) for r in rays)
    need(
        all(dot(row, k0) == dot(row, k1) == 0 for row in normalized),
        "normalized kernel",
    )
    need(all(dot(row, diag) == 0 for row in rows), "unnormalized extra kernel")
    need(lower_rank([k0, k1, diag]) == 3, "independent upper-rank certificates")
    # Ranks over the reals now coincide with their modular lower bounds.
    # Equivalent normalized totals differ by exactly u*k0+v*k1. A
    # target missing a zero-sum ray and a generic ray requires u,v>=0;
    # zero initial mass at the origin then requires -2u-9v>=0.
    for h in (0, 3):
        support = {ray(s) for s in orbit[h : h + 3]}
        need(len(support) == 3 and ORIGIN not in support, "target support")
        need(
            all(
                any(r not in support and class_group(r) == c for r in rays)
                for c in (2, 3)
            ),
            "missing positivity witnesses",
        )


def conditional_demands(orbit: tuple[Triple, ...]) -> None:
    bits = tuple(int(detector(s, 0)) for s in orbit)
    need(bits == (1, 1, 1, 0, 0, 0), "first detector on six raw inputs")
    weights = [
        tuple(sum((k + j) % 6 == i for j in (0, 1, 1, 2)) for i in range(6))
        for k in range(6)
    ]
    for branch in (0, 1):
        columns = [i for i, bit in enumerate(bits) if bit == branch]
        restricted = [tuple(row[i] for i in columns) for row in weights]
        need(lower_rank(restricted) == 3, "conditioned inputs cannot be separated")
    # For any fixed analyzer, q_i is its mean after raw input i, t its
    # desired branch mean. Clearing the conditioning denominators gives
    # restricted*(q_i-t)_i=0. Zero-probability branches give a zero row.
    # Rank three forces every q_i=t; this is not an extra input assumption.


def combine(coeffs: Triple, points: Basis) -> Triple:
    (a, b, c), (u, v, w) = coeffs, points
    return (
        (a * u[0] + b * v[0] + c * w[0]) % 5,
        (a * u[1] + b * v[1] + c * w[1]) % 5,
        (a * u[2] + b * v[2] + c * w[2]) % 5,
    )


def map_wall(orbit: tuple[Triple, ...]) -> None:
    source = (orbit[0], orbit[1], orbit[2])
    bary = {
        combine(((1 - a - b) % 5, a, b), source): ((1 - a - b) % 5, a, b)
        for a, b in product(range(5), repeat=2)
    }
    need(
        set(bary) == {s for s in TAGS if sum(s) % 5 == 1},
        "three independent source points",
    )
    coords = tuple(bary[s] for s in orbit)
    labels = {scale(s, k): i for i, s in enumerate(orbit) for k in range(1, 5)}
    need(len(labels) == 24, "coincident projective codes")
    bright = [s for s, i in labels.items() if i < 3]
    need(len(bright) == 12 and len(TAGS) ** 3 == 5**9, "affine search universe")
    actions: dict[Row, set[Basis]] = defaultdict(set)
    varying_sum = 0
    for u, v, w in product(bright, repeat=3):
        targets = (u, v, w)
        label = tuple(labels.get(combine(c, targets), -1) for c in coords)
        if min(label[3:]) < 3:
            continue
        actions[label].add(targets)
        varying_sum += int(len({sum(s) % 5 for s in targets}) > 1)
    # Exhaustion: the three basis images determine every affine map on
    # the input plane. Positivity of an independent mixture excludes any
    # positive-weight component violating even one of the target supports.
    prescribed = {
        p + tuple(5 - p[2 - i] for i in range(3)) for p in permutations(range(3))
    }
    need(set(actions) == prescribed and varying_sum == 16, "ray-action classification")
    for tables in actions.values():
        x, y, z = next(iter(tables))
        need(
            tables == {(scale(x, k), scale(y, k), scale(z, k)) for k in range(1, 5)},
            "scalar copies",
        )
    # Common mixtures on this relaxed affine class are exactly six
    # nonnegative weights summing to 1, on the permutations above. The
    # dark block is the bright permutation conjugated by order reversal.
    # Every permutation spends exactly one middle-ray unit over the three
    # bright inputs. Reset to P0 needs 3*(2/4) = 3/2 such units, and P3
    # similarly needs 3/2 in the dark block. Already the former contradicts.
    need(
        all(p[:3].count(1) == p[3:].count(4) == 1 for p in actions),
        "middle-ray certificate",
    )
    p0 = (orbit[0], orbit[1], orbit[1], orbit[2])
    need(3 * p0.count(orbit[1]) > len(p0), "no strict budget mismatch")


def main() -> None:
    orbit = tuple(cycle((0, 1, 0), Six))
    tomography(orbit)
    conditional_demands(orbit)
    map_wall(orbit)
    print(
        "125 colors -> origin + 31 projective rays; 480 native analyzers, 240 distinct effects."
    )
    print(
        "Exact real ranks: effects 29, plus normalization 30/32. Positivity pins P0/P3 ray masses."
    )
    print(
        "Of 5^9 affine maps from the source plane to F5^3, 24 respect both supports: six ray permutations x four scalings."
    )
    print(
        "16 survivors even vary the output total across inputs. Each still spends 1 middle bright-ray unit; three resets require 3/2."
    )
    print(
        "No independent common affine mixture realizes these conditional statistics; memory-dependent control excluded."
    )


if __name__ == "__main__":
    main()
