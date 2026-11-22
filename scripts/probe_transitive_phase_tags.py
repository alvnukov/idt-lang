"""P3 optional raw-tag gate: no preferred tag under a transitive symmetry.

For a finite tag set S, seek a map T on ordered pairs that squares to swap
and commutes with every simultaneous relabeling in a transitive group K.
A *chosen* R in K must have order six and an actual six-cycle. We do not
require K to commute with R: preserving a particular clock frame is stronger.
No geometry, particle interpretation, or physical update is derived here.

Lower bounds (elementary arguments, not a Lean artifact):

1. For C6 alone, every six-cycle supplies one free orbit of ordered antipodes
   on which swap acts by R^3. T preserves the union of those orbits since
   it commutes with R and swap and preserves period. On the orbit indices
   T induces an involution with no fixed index: a shift by j on a single
   six-cycle cannot square to the shift by three. Thus there are an even
   number of six-cycles and at least 12 tags.

2. For transitive K, if n=|S| is even then 16 divides n. To see this,
   suppose the 2-part v of n is 2, 4, or 8. For a Sylow 2-subgroup P of K
   all P-orbits have length at least v by orbit-stabilizer, and an odd
   number have length v (reduce their sum modulo 2v). Choose a P-stabilizer
   conjugacy type H with odd multiplicity k among these smallest orbits.
   In X=Fix_S(H) every P-point stabilizer is H itself (maximal possible
   order). Exactly the chosen k orbits contribute to X, with one regular
   W=N_P(H)/H orbit apiece. The normalizer condition in a finite p-group
   gives 1<|W|<=v. T restricts to a W-equivariant swap root on X^2.

   Write q=|W| and i=#elements w satisfying w^2=1. On X^2/W, swap has
   (q*k^2-i*k)/2 transpositions: only pairs (x,wx), w^2=1, in a single
   W-sheet contribute fixed orbits. A square permutation must be even.
   This excludes C4, C8, D8 (order eight), Q8 since k is odd and
   (q,i) is (4,2), (8,2), (8,6), (8,2), respectively.
   For C2, C2^2, C4xC2 and C2^3 choose a nonsquare involution a. T preserves
   the graph y=ax, characterized by swap(u)=a.u. On its k free W-orbits,
   T^2 acts by a, so its induced involution fixes at least one orbit. There
   T is a translation whose square must be a, impossible. These cases
   exhaust groups of orders 2, 4, 8. No census of larger groups is used.

Hence 13 is the absolute transitive minimum: the affine F13 construction
below attains it. If R is free (in particular if R is a regular translation)
then 6|n and therefore 48|n. A nonabelian regular example below attains 48.
If a transitive group must also preserve the chosen frame (commute with R),
all tags have the same R-period, hence six. These are finite model-selection
costs under supplied symmetry assumptions.

Regular criterion: in coordinates (x,xd), T=(x f(d),x f(d)p(d)), so
p^2(d)=d^-1 and f(d)f(p(d))=d. An even number of nontrivial inverse
pairs is necessary; pair them in fours (d,e,d^-1,e^-1), taking f values
(1,d,d^-1 e,e^-1). Involutions fixed by p need square roots; two paired
involutions d,e need a^-1 d a=e, then f takes values a,a^-1 d. Thus every
odd-size conjugacy class of involutions must be square-valued. Together
these conditions suffice (the identity may be fixed).
"""

from __future__ import annotations

from collections.abc import Sequence
from itertools import product

Perm = tuple[int, ...]


def require(test: bool, message: str) -> None:
    if not test:
        raise ValueError(message)


def extend(seed: int, image: int, generators: Sequence[Perm]) -> dict[int, int] | None:
    """Unique equivariant map on the seed orbit with the prescribed seed image."""
    graph = {seed: image}
    queue = [seed]
    for a in queue:
        for g in generators:
            b, y = g[a], g[graph[a]]
            if b not in graph:
                graph[b] = y
                queue.append(b)
            elif graph[b] != y:
                return None
    return graph


def root_on_pairs(gens: Sequence[Perm]) -> Perm | None:
    """Complete for the given generators; no enumeration of transitive groups."""
    n = len(gens[0])
    require(all(sorted(g) == list(range(n)) for g in gens), "non-permutation")
    swap = tuple(j * n + i for i in range(n) for j in range(n))
    lifts = [tuple(g[i] * n + g[j] for i in range(n) for j in range(n)) for g in gens]
    joint = [*lifts, swap]
    residual = {i for i in range(n * n) if i != swap[i]}
    blocks = []
    while residual:
        seed = min(residual)
        identity_orbit = extend(seed, seed, joint)
        if identity_orbit is None:
            raise ValueError("identity map")
        blocks.append(tuple(sorted(identity_orbit)))
        residual.difference_update(identity_orbit)
    root = list(range(n * n))
    while blocks:
        block = blocks.pop(0)
        for y in block:
            f = extend(block[0], y, joint)
            if f is not None and f[y] == swap[block[0]]:
                for a, target in f.items():
                    root[a] = target
                break
        else:
            # Equal-sized transitive orbits with a map between them are isomorphic.
            # Self-rootability is invariant under isomorphism commuting with swap.
            for j, other in enumerate(blocks):
                if len(other) != len(block):
                    continue
                for z in other:
                    bridge = extend(block[0], z, joint)
                    if bridge is not None:
                        for a, target in bridge.items():
                            root[a], root[target] = target, swap[a]
                        break
                else:
                    continue
                blocks.pop(j)
                break
            else:
                return None
    require(sorted(root) == list(range(n * n)), "root is not bijective")
    require(all(root[root[a]] == swap[a] for a in range(n * n)), "root square")
    require(
        all(root[g[a]] == g[root[a]] for a in range(n * n) for g in lifts), "covariance"
    )
    return tuple(root)


def compose(a: Perm, b: Perm) -> Perm:
    return tuple(a[i] for i in b)


def closure(gens: Sequence[Perm]) -> list[Perm]:
    identity = tuple(range(len(gens[0])))
    found = {identity}
    queue = [identity]
    for p in queue:
        for g in gens:
            gp = compose(g, p)
            if gp not in found:
                found.add(gp)
                queue.append(gp)
    return queue


def periods(p: Perm) -> list[int]:
    rest = set(range(len(p)))
    lengths = []
    while rest:
        a = min(rest)
        length = 0
        while a in rest:
            rest.remove(a)
            length += 1
            a = p[a]
        lengths.append(length)
    return sorted(lengths)


def abelian(moduli: tuple[int, ...]) -> list[Perm]:
    tags = list(product(*(range(m) for m in moduli)))
    return [
        tuple(
            tags.index(tuple((a + int(i == j)) % moduli[i] for i, a in enumerate(tag)))
            for tag in tags
        )
        for j in range(len(moduli))
    ]


def dihedral_or_quaternion(twist: int) -> list[Perm]:
    # r^4=1, s r s^-1=r^-1, s^2=r^twist (0: D8, 2: Q8).
    tags = list(product(range(4), range(2)))
    return [
        tuple(tags.index(((i + 1) % 4, j)) for i, j in tags),
        tuple(tags.index(((-i + twist * j) % 4, 1 - j)) for i, j in tags),
    ]


def small_two_group_checks() -> None:
    rows = [
        ("C2", abelian((2,)), 2),
        ("C4", abelian((4,)), 2),
        ("V4", abelian((2, 2)), 4),
        ("C8", abelian((8,)), 2),
        ("D8", dihedral_or_quaternion(0), 6),
        ("Q8", dihedral_or_quaternion(2), 2),
        ("C4xC2", abelian((4, 2)), 4),
        ("C2^3", abelian((2, 2, 2)), 8),
    ]
    for name, gens, inv_count in rows:
        q = len(gens[0])
        group = closure(gens)
        identity = tuple(range(q))
        require(len(group) == len({g[0] for g in group}) == q, name + ": regular")
        invs = {g for g in group if compose(g, g) == identity}
        squares = {compose(g, g) for g in group}
        require(len(invs) == inv_count, name + ": involution count")
        parity_wall = (q - inv_count) % 4 == 2
        nonsquare_central = any(
            all(compose(a, g) == compose(g, a) for g in group) for a in invs - squares
        )
        require(parity_wall or nonsquare_central, name + ": missing obstruction")
        for k in (1, 3):
            sheets = [
                tuple(s * q + g[x] for s in range(k) for x in range(q)) for g in gens
            ]
            require(root_on_pairs(sheets) is None, name + ": unexpected root")


def check_root(root: Perm, group: Sequence[Perm]) -> None:
    n = len(group[0])
    require(sorted(root) == list(range(n * n)), "all pairs bijection")
    for i, v in enumerate(root):
        x, y = divmod(i, n)
        a, b = divmod(v, n)
        require(root[v] == y * n + x, "all pairs square")
        for g in group:
            require(root[g[x] * n + g[y]] == g[a] * n + g[b], "all relabelings")


def affine_thirteen() -> None:
    n = 13
    group = [
        tuple((a * x + b) % n for x in range(n)) for a in range(1, n) for b in range(n)
    ]
    require(
        len(set(group)) == 156 and len({g[0] for g in group}) == n,
        "affine transitivity",
    )
    clock = tuple(4 * x % n for x in range(n))
    require(clock in group and periods(clock) == [1, 6, 6], "clock on thirteen")
    # 5^2=-1 and 11*(1+5)=1 in F13.
    root = tuple(
        (x + 11 * (y - x)) % n * n + (x + 16 * (y - x)) % n
        for x in range(n)
        for y in range(n)
    )
    check_root(root, group)


def nonabelian_forty_eight() -> None:
    # (u,i,j)(v,h,l)=(u+(-1)^i v,i+h,j+l) in C3 semidirect by C4xC4.
    tags = list(product(range(3), range(4), range(4)))

    def left(u: int, i: int, j: int) -> Perm:
        return tuple(
            tags.index(((u + (-1) ** (i % 2) * v) % 3, (i + h) % 4, (j + l) % 4))
            for v, h, l in tags
        )

    gens = [left(1, 0, 0), left(0, 1, 0), left(0, 0, 1)]
    group = closure(gens)
    require(len(group) == len({g[0] for g in group}) == 48, "order/regularity")
    require(
        compose(gens[0], gens[1]) != compose(gens[1], gens[0]), "commutativity control"
    )
    clock = left(1, 0, 2)
    require(clock in group and periods(clock) == [6] * 8, "free six-clock")
    squares = {compose(g, g) for g in group}
    invs = {g for g in group if compose(g, g) == tuple(range(48))}
    require(len(invs) == 4 and invs <= squares, "regular criterion")
    root = root_on_pairs(gens)
    if root is None:
        raise ValueError("missing regular nonabelian root")
    check_root(root, group)


def main() -> None:
    small_two_group_checks()
    affine_thirteen()
    nonabelian_forty_eight()
    print(
        "Sylow obstruction controls: eight groups of orders 2/4/8; one and three free sheets reject."
    )
    print(
        "13 tags: all 169 pairs and 156 affine relabelings pass; chosen R has periods 1+6+6."
    )
    print(
        "48 tags: all 2304 pairs and 48 nonabelian regular relabelings pass; R has eight six-cycles."
    )
    print(
        "Finite raw-tag gate only; the affine thirteen-tag clock has one distinguished fixed point in that frame."
    )


if __name__ == "__main__":
    main()
