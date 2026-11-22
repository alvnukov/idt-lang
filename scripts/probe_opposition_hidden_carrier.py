"""How many classical states reproduce the fixed six-preparation Pauli dictionary?

This is a single-system test, not a derivation of states or measurement.
Assume exact probabilities for six signed-axis preparations, three sharp
binary tests with post-measurement repreparation, arbitrary sequences of
the specified quarter-turns, a fixed linear response and memoryless
positive stochastic dynamics on a finite classical carrier. An unrecorded
phase reference, apparatus memory, preparation-dependent control, or
approximation changes this question.
"""

from __future__ import annotations

from fractions import Fraction as F
from itertools import combinations, product

from scripts import probe_balanced_phase_composition as b
from scripts.probe_opposition_clock_scatter import FLAGS, G, advance, chart, extend
from scripts.probe_three_opposition_origin import DUAL, SHEET, WORDS, TupleI, X, need


def compose(a: TupleI, c: TupleI) -> TupleI:
    return tuple(a[k] for k in c)


def turns() -> set[TupleI]:
    gens = {extend(u, v, False) for u, v in FLAGS}
    seen = {X}
    todo = [X]
    while todo:
        p = todo.pop()
        for q in gens:
            y = compose(p, q)
            if y not in seen:
                seen.add(y)
                todo.append(y)
    return seen


def prep(vertices: tuple[TupleI, ...], label: int) -> tuple[F, ...]:
    support = sum(label in v for v in vertices)
    return tuple(F(int(label in v), support) for v in vertices)


def readout_controls() -> None:
    rotation = turns()
    sheet_group = {p for p in G if not chart(p)[0]}
    need(
        len(rotation) == len(sheet_group) == 24 and len(rotation & sheet_group) == 12,
        "distinct embedded symmetry groups",
    )
    for vertices in (SHEET, tuple(WORDS)):
        for x, y in product(X, repeat=2):
            state = prep(vertices, x)
            prob = sum(p for p, v in zip(state, vertices, strict=True) if y in v)
            need(
                prob == (int(x == y) if x // 2 == y // 2 else F(1, 2)),
                "single-system preparation/test",
            )
    # Four states: columns of the preparation map span R4 (four independent
    # columns suffice). A fixed linear update on all six preparations is thus
    # UNIQUE; a negative entry cannot be repaired by picking a stochastic map.
    rows = tuple(prep(SHEET, x) for x in X)
    need(
        any(b.determinant(tuple(rows[x] for x in c)) != 0 for c in combinations(X, 4)),
        "rank-four preparations",
    )
    for p in rotation:
        dual, ports = chart(p)
        u = b.matrix(
            tuple(tuple(int(ports[j] == i) for j in range(4)) for i in range(4))
        )
        if dual:
            u = b.multiply(
                u,
                b.matrix(
                    tuple(
                        tuple(F(1, 2) - int(i == j) for j in range(4)) for i in range(4)
                    )
                ),
            )
        for x in X:
            out = tuple(sum(t * w for t, w in zip(r, rows[x], strict=True)) for r in u)
            need(out == rows[p[x]], "unique induced tetra action")
        need(
            min(z for r in u for z in r) == (F(-1, 2) if dual else F(0)),
            "stochastic four-state wall",
        )
        # All rotations ARE permutations on the eight completions.
        vertex_perm = tuple(WORDS.index(tuple(sorted(p[x] for x in w))) for w in WORDS)
        for x in X:
            old = prep(WORDS, x)
            need(
                tuple(old[vertex_perm.index(i)] for i in range(8)) == prep(WORDS, p[x]),
                "eight-state escape",
            )
    # Six states: the partial marks themselves are ontic labels; use a fair
    # stochastic response on different axes. After either outcome, reset to
    # its eigenpreparation. This realizes arbitrary future Pauli-test words.
    for x, axis in product(X, range(3)):
        answers = tuple(
            F(int(x == y)) if x // 2 == axis else F(1, 2)
            for y in (2 * axis, 2 * axis + 1)
        )
        need(sum(answers) == 1, "six-state instrument")


def minimality_controls() -> None:
    rot = turns()
    # A covariant finite 3D polytope contains at least six vertices and has
    # at least six facets: every nonzero vector or outward facet normal has
    # orbit size >=6, since its SO(3) stabilizer consists of rotations about
    # that axis; the largest rotation order in this group is 4.
    orders = []
    for p in rot:
        v = p
        n = 1
        while v != X:
            v = compose(p, v)
            n += 1
        orders.append(n)
    need(
        set(orders) == {1, 2, 3, 4} and len(rot) // max(orders) == 6,
        "polytope orbit bound",
    )
    # With m<=5 hidden states, the affine span of all reachable preparations
    # has d>=3 from the six Pauli vectors, and d<=m-1. Dynamics and the correct
    # expected response extend linearly to that span. Its intersection with
    # the simplex is forward invariant. The image P under the three expected
    # responses is a 3-polytope invariant under all rotations (inverse words
    # are available in the visible group; no hidden stochastic inverse needed).
    # For d=3 this image is affinely isomorphic to a slice with <=m facets;
    # for d=4,m=5 it is the image of a whole simplex with <=5 vertices.
    # Both contradict the orbit count. No deterministic responses were assumed.
    need(
        [(m, d) for m in range(1, 6) for d in range(3, m)] == [(4, 3), (5, 3), (5, 4)],
        "lower-bound cases",
    )
    # If one demands simultaneous deterministic answers even on inaccessible
    # vertices AND a covariant action on those assignments, the minimum rises
    # to eight: the orbit of any sign word is all eight cube vertices.
    start = WORDS[0]
    need(
        {tuple(sorted(p[x] for x in start)) for p in rot} == set(WORDS),
        "eight required under deterministic covariant assignment",
    )
    need(
        set(SHEET) | set(DUAL) == set(WORDS)
        and len({advance(X, p) for p in rot}) == 24,
        "faithful action",
    )


def main() -> None:
    readout_controls()
    minimality_controls()
    print(
        "Six partial preparations on four equiprobable completions reproduce all single Pauli-axis probabilities. Twelve of the 24 proper signed-axis rotations act by tetrahedron permutations; the other twelve require a negative entry -1/2 on that four-state carrier."
    )
    print(
        "Six classical states suffice with stochastic responses and reset; fewer than six cannot realize all exact reusable rotations under fixed finite Markov dynamics and linear readout. Eight completions suffice if every axis already has a deterministic covariant value. No composite, Bell, spin or single-event origin follows."
    )


if __name__ == "__main__":
    main()
