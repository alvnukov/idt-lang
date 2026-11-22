"""Which assumptions specify the spectator and which do not?

The raw carrier, distinguished spectator role, F5 affine relabelings,
and square-to-target-swap are assumptions. This is a finite classification
of deterministic contact rules, not a symmetry inferred from experiments.
Relaxing target-sum conservation makes the candidate nonunique; demanding
equivariance under *every* permutation of five unstructured symbols instead
removes even this candidate. Classical reversible programmability is a
control on how much one should infer from its six-setting quantum table.
"""

from itertools import permutations, product

from scripts.probe_affine_pulse_holdouts import need
from scripts.probe_midpoint_spectator_instrument import Contact, apply, rule

Q = tuple(range(5))
Tab = tuple[int, ...]
Law = tuple[Tab, Tab]


def normalized(law: Law, s: int, x: int, y: int) -> tuple[int, int]:
    if x == y:
        return x, y
    # d = y-x, r = (m-s)/d. Scale and translation covariance leave only
    # the output ratio p(r) and the multiplier h(r) of d to choose.
    p, h = law
    d = (y - x) % 5
    m = (3 * (x + y)) % 5
    r = ((m - s) * pow(d, -1, 5)) % 5
    dd = d * h[r] % 5
    mm = (s + p[r] * dd) % 5
    return (mm - 3 * dd) % 5, (mm + 3 * dd) % 5


def census() -> tuple[set[Law], set[Law]]:
    # Keep equal targets fixed; the square law makes the complement an
    # invariant permutation set. Every one of five scale-orbits of unequal
    # targets has four members, so an invertible equivariant map permutes
    # the orbits p and chooses one of four nonzero multipliers on each.
    # SWAP is precisely (r,d) -> (-r,-d) in these coordinates.
    laws = {
        (p, h)
        for p in permutations(Q)
        if all(p[p[r]] == (-r) % 5 for r in Q)
        for h in product(range(1, 5), repeat=5)
        if all(h[r] * h[p[r]] % 5 == 4 for r in Q)
    }
    preserve: set[Law] = set()
    for law in laws:
        ok = True
        for s, x, y in product(Q, repeat=3):
            a, b = normalized(law, s, x, y)
            need(normalized(law, s, a, b) == (y, x), "square law")
            ok &= (a + b - x - y) % 5 == 0
            for k, t in product(range(1, 5), Q):
                need(
                    normalized(law, (k * s + t) % 5, (k * x + t) % 5, (k * y + t) % 5)
                    == ((k * a + t) % 5, (k * b + t) % 5),
                    "affine frame",
                )
        if ok:
            preserve.add(law)
    need(len(laws) == 16 and len(preserve) == 4, "full and conserved census")
    return laws, preserve


def conserved_crosscheck(preserve: set[Law]) -> None:
    # Independent direct parameterization: normalize the target (x,y) to
    # (0,1). Scan arbitrary left output on each of the five spectators,
    # NOT just the selected two branches. The right follows by conservation.
    winners: set[Tab] = set()
    for left in product(Q, repeat=5):
        for s, a in enumerate(left):
            b = (1 - a) % 5
            if b == a:
                break  # an unequal pair cannot map to the diagonal
            d = (b - a) % 5
            if (a + d * left[(s - a) * pow(d, -1, 5) % 5]) % 5 != 1:
                break
        else:
            winners.add(left)
    rows = {tuple(normalized(law, s, 0, 1)[0] for s in Q) for law in preserve}
    need(
        winners
        == rows
        == {(2, 2, 2, 2, 2), (4, 4, 4, 4, 4), (2, 2, 2, 4, 2), (4, 4, 4, 2, 4)},
        "not all conserved roots",
    )
    chosen = tuple(rule(s, 0, 1)[0] for s in Q)
    need(chosen in rows and len(set(chosen)) == 2, "new law not in census")
    for s, x, y in product(Q, repeat=3):
        nonlinear = [
            normalized(law, s, x, y)
            for law in preserve
            if len({normalized(law, t, 0, 1)[0] for t in Q}) == 2
        ]
        p, q = rule(s, x, y)
        need(sorted(nonlinear) == sorted([(p, q), (q, p)]), "nonlinear inverse pair")


def unstructured_control() -> None:
    # S5 case. Given spectator=target x=0 and y=1, any equivariant
    # deterministic output is fixed by all permutations of other labels.
    # Only 0 and 1 are fixed. Equal output coordinates are impossible
    # because a square root of SWAP commutes with SWAP and is bijective.
    # Both orderings therefore form an invariant pair of raw states for
    # this fixed spectator. Neither permutation of two objects squares to
    # their transposition. This uses no conservation or field arithmetic.
    fix = [p for p in permutations(Q) if p[:2] == (0, 1)]
    possible = [
        (u, v)
        for u, v in permutations(Q, 2)
        if all((p[u], p[v]) == (u, v) for p in fix)
    ]
    need(
        set(possible) == {(0, 1), (1, 0)}
        and all(tuple(p[p[i]] for i in (0, 1)) == (0, 1) for p in permutations((0, 1))),
        "equality-only root",
    )


def reversible_control() -> None:
    # An ordinary conservative Boolean controlled-SWAP with unchanged
    # helper *values*. Completed macros on external addresses do not turn
    # classical reversibility into a measurement primitive of nature.
    word: tuple[Contact, ...] = (
        (0, 5, 6),
        (3, 5, 6),
        (5, 1, 2),
        (4, 1, 2),
        (0, 5, 6),
        (3, 5, 6),
    )
    for b, a in permutations(Q, 2):
        frame = tuple((b + (a - b) * i) % 5 for i in Q)
        for c, x, y in product(range(2), repeat=3):
            v = [frame[i] for i in (c, x, y, 1, 3, 4, 3)]
            original = v.copy()
            apply(v, word)
            expected = original.copy()
            if c:
                expected[1], expected[2] = expected[2], expected[1]
            need(v == expected, "Fredkin with restored stocks")


def main() -> None:
    _, keep = census()
    conserved_crosscheck(keep)
    unstructured_control()
    reversible_control()
    print(
        "Fixed spectator/diagonal, affine-tag covariance and target square-to-swap: 16 roots on F5; target-sum conservation leaves 4."
    )
    print(
        "Two ignore the spectator. The only interacting conserved pair choose opposite orientations exactly at the midpoint; they are inverses."
    )
    print(
        "Pure equality on five fully interchangeable tags has no spectator-fixed square root of target SWAP."
    )
    print(
        "Six contacts implement ordinary Boolean Fredkin with restored helper values, all 160 bit/frame cases: supplied circuits are a major resource."
    )


if __name__ == "__main__":
    main()
