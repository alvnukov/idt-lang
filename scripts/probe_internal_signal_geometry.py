"""What can an internal clock learn from paths through identical four-port junctions?

The input is two alternating roles joined by four named relations, NOT a
three-dimensional embedding. We supply two different rules for identifying
endpoints of path histories. A clock counts one tick per link; an observer can
recognize a reunion, address a chosen port, and compare repeated experiments.
Those are operational hypotheses, not consequences of the opposition primitive.
"""

from collections import Counter
from fractions import Fraction as F
from itertools import pairwise, permutations, product

Point = tuple[int, ...]
PORTS = range(4)
ZERO: Point = (0, 0, 0, 0)


def need(ok: bool, msg: str) -> None:
    if not ok:
        raise ValueError(msg)


def endpoint(path: tuple[int, ...], abelian: bool) -> Point:
    if not abelian:
        # The universal cover recognizes only immediate reversal and its
        # consequences. A reduced word uniquely names a reached junction.
        reduced: list[int] = []
        for port in path:
            if reduced and reduced[-1] == port:
                reduced.pop()
            else:
                reduced.append(port)
        return tuple(reduced)
    counts = list(ZERO)
    for i, port in enumerate(path):
        counts[port] += (-1) ** i
    return tuple(counts)


def abelian_shells(radius: int, modulus: int = 0) -> list[set[Point]]:
    """BFS using only traversals and the supplied endpoint equality."""
    shell = {ZERO}
    seen = set(shell)
    shells = [shell]
    for step in range(radius):
        sign = (-1) ** step
        reached: set[Point] = set()
        for x in shell:
            for port in PORTS:
                y = list(x)
                y[port] += sign
                if modulus:
                    y[port] %= modulus
                reached.add(tuple(y))
        shell = reached - seen
        seen.update(shell)
        shells.append(shell)
    return shells


def local_reunion_controls(radius: int = 6) -> tuple[int, int, int]:
    """Generate endpoint classes by local changes, without supplying count keys.

    A traverse followed by its inverse vanishes. Supply one more symmetric
    rule: walking abc or cba ends at the same junction. For distinct a,b,c
    this says abcabc closes; repeats already follow from cancellation.
    Replacing any subpath is allowed (history-independent junction identity).
    A swap exchanges adjacent entries of the same parity. Thus ports at each
    parity can be ordered, and matching opposite-parity entries brought
    together and cancelled. Their signed multiplicities are a complete
    invariant for the *least* such path equality; extra relations can remain.
    Below, compute bounded classes first and compare them with counts second.
    """
    words = [p for k in range(radius + 1) for p in product(PORTS, repeat=k)]
    parent = list(range(len(words)))
    indices = {w: i for i, w in enumerate(words)}

    def root(i: int) -> int:
        while i != parent[i]:
            parent[i] = parent[parent[i]]
            i = parent[i]
        return i

    for i, w in enumerate(words):
        for j, (a, b) in enumerate(pairwise(w)):
            if a == b:
                shorter = w[:j] + w[j + 2 :]
                parent[root(i)] = root(indices[shorter])
        for j in range(len(w) - 2):
            swapped = w[:j] + w[j : j + 3][::-1] + w[j + 3 :]
            parent[root(i)] = root(indices[swapped])
    observed = {(root(i), endpoint(w, True)) for i, w in enumerate(words)}
    components = len({i for i, _ in observed})
    need(
        components == len(observed) == len({x for _, x in observed}),
        "rule-generated and signed-count endpoints disagree",
    )

    # Countermodel: four star transpositions on five anonymous tokens.
    # All ports equivalent, steps are self-inverse, minimum loop is ALSO six.
    # But ababab closes, while abcabc on distinct ports does not.
    def star(w: tuple[int, ...]) -> Point:
        s = list(range(5))
        for p in w:
            s[0], s[p + 1] = s[p + 1], s[0]
        return tuple(s)

    loops = [
        w
        for w in words
        if w and all(a != b for a, b in pairwise(w)) and star(w) == star(())
    ]
    need(
        set(loops) == {(a, b) * 3 for a, b in permutations(PORTS, 2)},
        "different symmetric girth-six endpoint rule",
    )
    need(len({star(w) for w in words}) == 120, "star permutations")
    return len(words), components, len(loops)


def cover_controls() -> tuple[list[int], F]:
    shells = abelian_shells(12)
    sizes = list(map(len, shells))
    for i, shell in enumerate(shells):
        need(all(sum(x) == i % 2 for x in shell), "alternating role")
        need(all(sum(map(abs, x)) == i for x in shell), "tick distance")
        if i > 0 and i % 2 == 0:
            need(len(shell) == 10 * (i // 2) ** 2 + 2, "rank-three growth control")
    tree = []
    for k in range(5):
        tree.append(
            len(
                {
                    endpoint(p, False)
                    for p in product(PORTS, repeat=k)
                    if all(a != b for a, b in pairwise(p))
                }
            )
        )
    need(tree == [1, 4, 12, 36, 108], "tree shells")
    need(sizes[:4] == [1, 4, 12, 24], "first detectable shell")
    need(sizes[:3] == tree[:3], "two-tick ambiguity")
    words = [p for p in product(PORTS, repeat=6) if all(a != b for a, b in pairwise(p))]
    closed = {p for p in words if endpoint(p, True) == ZERO}
    need(closed == {s + s for s in permutations(PORTS, 3)}, "six-tick reunion protocol")
    need(all(endpoint(p, False) for p in words), "no tree reunion")
    rate = F(len(closed), len(words))
    need(rate == F(2, 81), "uniform non-retracing closure rate")
    # A finite quotient can imitate every equality within a bounded radius.
    mod = 26
    finite = abelian_shells(12, mod)
    for a, b in zip(shells, finite, strict=True):
        need(
            {tuple(i % mod for i in x) for x in a} == b and len(a) == len(b),
            "finite quotient impersonator",
        )
    return sizes, rate


def clock_control() -> tuple[int, int]:
    # Four observer stations named by paths only; locate pairwise distances
    # from the BFS shells, NOT from an assumed spatial norm.
    positions = [endpoint(p, True) for p in ((), (1, 0), (1, 0, 3, 2), (3, 2))]
    distances = {x: k for k, shell in enumerate(abelian_shells(4)) for x in shell}

    def d(i: int, j: int) -> int:
        return distances[tuple(a - b for a, b in zip(positions[i], positions[j]))]

    sides = [d(i, (i + 1) % 4) for i in PORTS]
    diag = d(0, 2) * d(1, 3)
    bound = sides[0] * sides[2] + sides[1] * sides[3]
    need(sides == [2] * 4 and (diag, bound) == (16, 8), "Ptolemy obstruction")
    return diag, bound


def diffusion_control() -> list[list[F]]:
    # Two independent port choices supplied by a known sampling protocol.
    steps = [endpoint(p, True) for p in product(PORTS, repeat=2)]
    need(all(sum(x[i] for x in steps) == 0 for i in PORTS), "unbiased increments")
    cov = [[F(sum(x[i] * x[j] for x in steps), 16) for j in PORTS] for i in PORTS]
    need(
        all(cov[i][j] == F(4 * int(i == j) - 1, 8) for i in PORTS for j in PORTS),
        "measured covariance",
    )
    # Check its three eigenvectors on the zero-sum count lattice and its null.
    basis = [endpoint((i, 0), True) for i in range(1, 4)]
    for v in basis:
        need(
            all(sum(cov[i][j] * v[j] for j in PORTS) == F(v[i], 2) for i in PORTS),
            "rank-three covariance",
        )
    need(all(sum(row) == 0 for row in cov), "redundant count vanishes")
    # Bias is an observational rival even with the same reachable endpoints.
    bias = (1, 1, 1, 5)
    alt = Counter({(i, j): bias[i] * bias[j] for i, j in product(PORTS, repeat=2)})
    var = [
        F(sum(w * endpoint(p, True)[i] ** 2 for p, w in alt.items()), 64) for i in PORTS
    ]
    need(var == [F(7, 32)] * 3 + [F(15, 32)], "nonuniform control")
    return cov


def main() -> None:
    words, components, star_loops = local_reunion_controls()
    sizes, rate = cover_controls()
    diag, bound = clock_control()
    cov = diffusion_control()
    print(
        f"Equal local four-port rules: tree/abelian shells agree at r<=2; abelian r=0..6: {sizes[:7]}."
    )
    print(f"Six-tick non-retracing reunion: {rate} (uniform protocol) vs zero (tree).")
    print(
        f"Local abc=cba and retrace rules recover all {components} count classes on {words} histories; finite wrap imitates twelve ticks."
    )
    print(
        f"Other symmetric four-port world: {star_loops} rooted non-retracing returns by tick six, all ababab, not abcabc."
    )
    print(f"Shortest-clock Ptolemy: {diag} > {bound}; not Euclidean in any dimension.")
    print(
        f"Uniform two-tick covariance first row {list(map(str, cov[0]))}: rank three, isotropic on contrasts."
    )
    print(
        "A conditional internal signal discriminator, not a derivation of physical space, observers or gravity."
    )


if __name__ == "__main__":
    main()
