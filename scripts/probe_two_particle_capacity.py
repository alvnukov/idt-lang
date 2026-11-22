"""Exact controls for finite number-preserving roots of the port swap.

With no extra state, T commutes with swap S because T² = S. Each nontrivial
S-orbit must be paired with another in a four-cycle. A distinct unordered
single-label pair is therefore a bunching edge only by consuming one
vacuum/double-label orbit. By covariance any diagonal input stays diagonal,
hence stays split at total number two. The roots below fix diagonals outright.

For iid single-label weights p, C = 1 - 2 sum_edges p[i] p[j]. The graph
optimization does not assume uniform weights: if two positive weights occupy
nonadjacent vertices, the edge sum is linear in their reallocation, so moving
their combined mass to one endpoint can only improve its maximum. Iterate
until the support is a clique; there C is sum p[i]², minimized by uniform
weights on a largest clique. The finite grid below is a regression check of
this argument, not a substitute for it or a check of arbitrary physics.
"""

from collections import Counter, defaultdict
from collections.abc import Iterable, Iterator, Sequence
from dataclasses import dataclass
from fractions import Fraction
from itertools import combinations, product
from math import comb


@dataclass(frozen=True)
class Label:
    name: str
    number: int
    marker: int = 0


Pair = tuple[Label, Label]
Edge = tuple[int, int]
Counts = tuple[int, int, int]
Sector = tuple[int, int]


def require(condition: bool, message: str) -> None:
    if not condition:
        raise AssertionError(message)


def swap(pair: Pair) -> Pair:
    return pair[1], pair[0]


def sector(pair: Pair) -> Sector:
    left, right = pair
    return left.number + right.number, left.marker + right.marker


def orbit(pair: Pair) -> frozenset[Label]:
    return frozenset(pair)


def make_root(
    labels: Sequence[Label], matched: Sequence[tuple[Pair, Pair]]
) -> dict[Pair, Pair]:
    result: dict[Pair, Pair] = {(label, label): (label, label) for label in labels}
    unused = {orbit(pair): pair for pair in combinations(labels, 2)}

    def pair_orbits(first: Pair, second: Pair) -> None:
        require(sector(first) == sector(second), "matched orbit sectors disagree")
        del unused[orbit(first)], unused[orbit(second)]
        cycle = (first, second, swap(first), swap(second))
        result.update(zip(cycle, (*cycle[1:], cycle[0]), strict=True))

    for first, second in matched:
        pair_orbits(first, second)

    remaining: dict[Sector, list[Pair]] = defaultdict(list)
    for pair in unused.values():
        remaining[sector(pair)].append(pair)
    for key, pairs in remaining.items():
        if len(pairs) % 2:
            raise ValueError(f"odd number of unmatched swap orbits in sector {key}")
        for first, second in zip(pairs[::2], pairs[1::2], strict=True):
            pair_orbits(first, second)
    require(not unused, "unpaired orbit")
    return result


def check_root(labels: Sequence[Label], root: dict[Pair, Pair]) -> int:
    states = set(product(labels, labels))
    require(set(root) == states == set(root.values()), "root is not a full permutation")
    for pair, out in root.items():
        require(root[out] == swap(pair), "root does not square to port swap")
        require(sector(out) == sector(pair), "root fails number or marker conservation")
        if pair[0] == pair[1]:
            require(out == pair, "diagonal was not fixed")
    return len(states)


def populations(outputs: Iterable[Pair]) -> Counts:
    counts: Counter[Sector] = Counter(
        (left.number, right.number) for left, right in outputs
    )
    result = counts[2, 0], counts[1, 1], counts[0, 2]
    require(sum(result) == counts.total(), "unexpected two-particle population")
    return result


def marked_exits(outputs: Iterable[Pair]) -> tuple[int, int]:
    left_count = right_count = 0
    for pair in outputs:
        require(sector(pair)[1] == 1, "expected exactly one marked particle")
        left_count += pair[0].marker
        right_count += pair[1].marker
    return left_count, right_count


def check_singles(
    root: dict[Pair, Pair], vacuum: Label, singles: Sequence[Label]
) -> None:
    for inputs in (
        [(label, vacuum) for label in singles],
        [(vacuum, label) for label in singles],
    ):
        exits = Counter(root[pair][0].number for pair in inputs)
        require(exits[0] == exits[1] == len(singles) // 2, "singles are not balanced")
        require(
            exits.total() == len(singles) and len(singles) % 2 == 0, "bad single sample"
        )


def bunching_edges(singles: Sequence[Label], root: dict[Pair, Pair]) -> set[Edge]:
    edges: set[Edge] = set()
    for i, left in enumerate(singles):
        require(root[left, left] == (left, left), "diagonal is a bunching input")
        for j in range(i + 1, len(singles)):
            right = singles[j]
            out = root[left, right]
            require(root[right, left] == swap(out), "port-swap covariance failed")
            if out[0].number != 1:
                edges.add((i, j))
    return edges


def clique(n: int, edges: set[Edge]) -> tuple[int, ...]:
    for size in range(n, 0, -1):
        for candidate in combinations(range(n), size):
            if all(edge in edges for edge in combinations(candidate, 2)):
                return candidate
    raise ValueError("empty graph has no single-label iid input")


def capacity_bound(n: int, vacua: int, doubles: int) -> int:
    return max(size for size in range(1, n + 1) if comb(size, 2) <= vacua * doubles)


def iid_coincidence(weights: Sequence[Fraction], edges: set[Edge]) -> Fraction:
    require(all(p >= 0 for p in weights) and sum(weights) == 1, "invalid iid weights")
    return Fraction(1) - 2 * sum(weights[i] * weights[j] for i, j in edges)


def mass_grid(n: int, mass: int) -> Iterator[tuple[int, ...]]:
    if n == 1:
        yield (mass,)
    else:
        for first in range(mass + 1):
            for rest in mass_grid(n - 1, mass - first):
                yield (first, *rest)


def check_graph_grid() -> tuple[int, int]:
    total_graphs = total_points = 0
    mass = 6
    for n in range(1, 6):
        candidates = tuple(combinations(range(n), 2))
        counts = list(mass_grid(n, mass))
        for mask in range(1 << len(candidates)):
            edges = {edge for i, edge in enumerate(candidates) if (mask >> i) & 1}
            support = clique(n, edges)
            k = len(support)
            weights = [Fraction(int(i in support), k) for i in range(n)]
            require(
                iid_coincidence(weights, edges) == Fraction(1, k),
                "clique bound not tight",
            )
            for p in counts:
                numerator = mass**2 - 2 * sum(p[i] * p[j] for i, j in edges)
                require(numerator * k >= mass**2, "grid point beats clique-bound floor")
            total_graphs += 1
            total_points += len(counts)
    return total_graphs, total_points


def literal_probe() -> tuple[int, Counts, Counts]:
    vacuum, a, b, double = Label("0", 0), Label("a", 1), Label("b", 1), Label("D", 2)
    labels = [vacuum, a, b, double]
    root = make_root(labels, [((a, b), (double, vacuum))])
    states = check_root(labels, root)
    check_singles(root, vacuum, [a, b])

    independent = list(product([a, b], [a, b]))
    anticorrelated = [(a, b), (b, a)]
    for pairs in (independent, anticorrelated):
        for port in range(2):
            marginal = Counter(pair[port] for pair in pairs)
            require(
                marginal[a] == marginal[b] == len(pairs) // 2, "marginal not uniform"
            )

    independent_counts = populations(root[pair] for pair in independent)
    anticorrelated_counts = populations(root[pair] for pair in anticorrelated)
    edges = bunching_edges([a, b], root)
    require(
        independent_counts == (1, 2, 1) and anticorrelated_counts == (1, 0, 1),
        "bad histograms",
    )
    require(
        len(edges) == 1 and len(clique(2, edges)) == capacity_bound(2, 1, 1) == 2,
        "bad capacity",
    )
    require(
        iid_coincidence([Fraction(1, 2)] * 2, edges) == Fraction(1, 2), "bad iid floor"
    )
    return states, independent_counts, anticorrelated_counts


def complete_probe(n: int) -> int:
    vacuum = Label("0", 0)
    singles = [Label(f"s{i}", 1) for i in range(n)]
    split_pairs = list(combinations(singles, 2))
    doubles = [Label(f"d{i}", 2) for i in range(len(split_pairs))]
    matches = list(
        zip(split_pairs, [(double, vacuum) for double in doubles], strict=True)
    )
    labels = [vacuum, *singles, *doubles]
    root = make_root(labels, matches)
    states = check_root(labels, root)
    edges = bunching_edges(singles, root)
    require(len(edges) == len(doubles), "complete-graph capacity not saturated")
    require(
        len(clique(n, edges)) == capacity_bound(n, 1, len(doubles)) == n, "wrong clique"
    )
    require(
        iid_coincidence([Fraction(1, n)] * n, edges) == Fraction(1, n),
        "wrong iid floor",
    )
    return states


def approximate_probe() -> tuple[
    int, int, int, int, tuple[Counts, Counts, Counts, Counts]
]:
    r = 8
    vacuum = Label("0", 0)
    u = [Label(f"u{i}", 1) for i in range(r)]
    m = [Label(f"m{i}", 1, 1) for i in range(r)]
    singles = [*u, *m]
    selected = [*combinations(u, 2), *combinations(m, 2)]
    left_marked_edges = [
        (left, right)
        for i, left in enumerate(u)
        for j, right in enumerate(m)
        if i % 2 == j % 2 == 0
    ]
    right_marked_edges = [
        (left, right)
        for i, left in enumerate(u)
        for j, right in enumerate(m)
        if i % 2 == j % 2 == 1
    ]
    selected.extend(left_marked_edges)
    selected.extend(right_marked_edges)
    double_labels = [
        Label(f"d{i}", 2, sector(pair)[1]) for i, pair in enumerate(selected)
    ]
    all_labels = [vacuum, *singles, *double_labels]
    right_marked_set = set(right_marked_edges)
    matches = [
        (pair, (vacuum, double) if pair in right_marked_set else (double, vacuum))
        for pair, double in zip(selected, double_labels, strict=True)
    ]
    root = make_root(all_labels, matches)
    states = check_root(all_labels, root)
    for group in (u, m):
        check_singles(root, vacuum, group)
    uu = populations(root[pair] for pair in product(u, u))
    mm = populations(root[pair] for pair in product(m, m))
    um = populations(root[pair] for pair in product(u, m))
    mu = populations(root[pair] for pair in product(m, u))
    require(uu == mm == (28, 8, 28) and um == mu == (16, 32, 16), "bad tag histogram")
    for first, second in ((u, m), (m, u)):
        out = [root[pair] for pair in product(first, second)]
        require(marked_exits(out) == (32, 32), "unconditional marked exits unbalanced")
        require(
            marked_exits(pair for pair in out if pair[0].number == 1) == (16, 16),
            "split exits unbalanced",
        )
        require(
            marked_exits(pair for pair in out if pair[0].number != 1) == (16, 16),
            "bunch exits unbalanced",
        )
    edges = bunching_edges(singles, root)
    expected = {
        (i, j)
        for i, j in combinations(range(2 * r), 2)
        if i // r == j // r or i % 2 == j % 2
    }
    require(edges == expected, "unexpected bunching graph")
    k = len(clique(len(singles), edges))
    bound = capacity_bound(len(singles), 1, len(double_labels))
    require((states, len(edges), k, bound) == (11025, 88, 8, 13), "bad capacity counts")
    require(
        iid_coincidence([Fraction(1, r)] * r + [Fraction(0)] * r, edges)
        == Fraction(1, r),
        "bad approximation floor",
    )
    return states, len(edges), k, bound, (uu, mm, um, mu)


def memory_probe() -> tuple[int, tuple[Counts, Counts, Counts, Counts]]:
    """Extra directed four-state memory: T² = port swap × phase+2, not swap alone."""
    vacuum, u, m = Label("0", 0), Label("u", 1), Label("m", 1, 1)
    uu, um, mm = Label("UU", 2), Label("UM", 2, 1), Label("MM", 2, 2)
    labels = (vacuum, u, m, uu, um, mm)
    g: dict[Pair, Pair] = {(u, u): (uu, vacuum), (u, m): (vacuum, um)}
    g.update({target: source for source, target in g.items()})

    def step(pair: Pair, phase: int) -> tuple[Pair, int]:
        # g, S g^-1, S g S, g^-1 S; here g^-1 = g.
        x = swap(pair) if phase in (2, 3) else pair
        y = g.get(x, x)
        return (swap(y) if phase in (1, 2) else y), (phase + 1) % 4

    states = {(pair, e) for pair in product(labels, labels) for e in range(4)}
    require(
        {step(*state) for state in states} == states, "memory step is not a permutation"
    )
    for pair, e in states:
        out, next_e = step(pair, e)
        require(
            sector(out) == sector(pair),
            "memory step does not conserve number or marker",
        )
        require(
            step(out, next_e) == (swap(pair), (e + 2) % 4),
            "undisturbed memory echo fails",
        )

    def outputs(pair: Pair) -> list[Pair]:
        return [step(pair, e)[0] for e in range(4)]

    for label in (u, m):
        for pair in ((label, vacuum), (vacuum, label)):
            require(
                Counter(outputs(pair)) == {pair: 2, swap(pair): 2},
                "memory singles unbalanced",
            )
    for pair in ((u, m), (m, u)):
        require(marked_exits(outputs(pair)) == (2, 2), "memory marked exits unbalanced")
    rows = (
        populations(outputs((u, u))),
        populations(outputs((m, m))),
        populations(outputs((u, m))),
        populations(outputs((m, u))),
    )
    require(
        rows == ((2, 0, 2), (0, 4, 0), (1, 2, 1), (1, 2, 1)), "bad memory histogram"
    )
    return len(states), rows


def main() -> None:
    graphs, grid_points = check_graph_grid()
    print(
        f"grid: {graphs} labeled graphs (1..5 vertices), {grid_points} weight points; exact clique minima"
    )
    states, iid, anti = literal_probe()
    print(
        f"literal: {states} states, balanced singles; iid={iid}/4 C=1/2; anticorrelated={anti}/2 C=0"
    )
    try:
        complete_probe(3)
    except ValueError as exc:
        require(
            str(exc) == "odd number of unmatched swap orbits in sector (1, 0)",
            "unexpected obstruction",
        )
    else:
        raise AssertionError(
            "three-label capacity fit misses a swap-orbit parity obstruction"
        )
    complete_states = complete_probe(8)
    print(
        f"capacity: K8 saturates 28 edges in {complete_states} states, iid floor 1/8; K3 sector parity blocks root"
    )
    states, edges, k, bound, (uu, mm, um, mu) = approximate_probe()
    print(
        f"r=8: {states} states, {edges} edges, clique={k}, capacity upper bound={bound}; balanced singles and marked exits"
    )
    print(f"r=8 raw (20,11,02): UU={uu}/64 MM={mm}/64 UM={um}/64 MU={mu}/64")
    memory_states, (uu, mm, um, mu) = memory_probe()
    print(
        f"memory: {memory_states} states, T^2=swap x phase+2; UU={uu}/4 MM={mm}/4 UM={um}/4 MU={mu}/4"
    )
    print(
        "PASS: finite controls only; no physical derivation or experimental validation"
    )


if __name__ == "__main__":
    main()
