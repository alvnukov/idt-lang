"""Finite signed-slot algebra benchmark on free integer spans of binary states.

For distinct i,j,l the imposed [Eij,Ejl] = Eil uses the two-step path
through an empty j in Eij Ejl, or through an occupied j in Ejl Eij.
Thus the reciprocal sign product around the triangle is +1 or -1,
respectively. Every Johnson triangle is one of these types. GF(2) below
encodes signs over the integers; it is not the operator coefficient ring.

The extra adjacent-sector data are not identified by the transfers: a sign
w(S) on each creation out of S and its reverse occurs twice in C_i+ C_j-.
These are supplied algebraic controls, not a derivation of CAR, a physical
symmetry group, spin, statistics, or the Standard Model.
"""

from collections.abc import Callable
from functools import partial
from itertools import combinations, permutations, product

Term = tuple[int, int] | None  # (basis mask, integer coefficient), or zero
Action = Callable[[int], Term]
Transfers = dict[tuple[int, int], Action]


def require(condition: bool, failure: object) -> None:
    if not condition:
        raise AssertionError(failure)


def occupied(state: int, slot: int) -> int:
    return (state >> slot) & 1


def sign(parity: int) -> int:
    return 1 - 2 * (parity % 2)


def between(state: int, i: int, j: int) -> int:
    return sum(occupied(state, h) for h in range(min(i, j) + 1, max(i, j)))


def transfer(i: int, j: int, signed: bool, state: int) -> Term:
    if not occupied(state, j):
        return None
    if i == j:
        return state, 1
    if occupied(state, i):
        return None
    return state ^ (1 << i) ^ (1 << j), sign(between(state, i, j)) if signed else 1


def transfers(n: int, signed: bool) -> Transfers:
    return {
        (i, j): partial(transfer, i, j, signed) for i, j in product(range(n), repeat=2)
    }


def pair(left: Action, right: Action, state: int) -> Term:
    first = right(state)
    if first is None:
        return None
    second = left(first[0])
    return None if second is None else (second[0], first[1] * second[1])


def combine(*terms: tuple[Term, int], modulus: int = 0) -> dict[int, int]:
    result: dict[int, int] = {}
    for term, factor in terms:
        if term is not None:
            state, coefficient = term
            result[state] = result.get(state, 0) + factor * coefficient
    if modulus:
        result = {state: value % modulus for state, value in result.items()}
    return {state: value for state, value in result.items() if value}


def check_matrix_units(
    n: int, states: list[int], signed: Transfers, plain: Transfers
) -> None:
    for a, b, c, d in product(range(n), repeat=4):
        for s in states:
            rhs = (signed[a, d](s), int(b == c)), (signed[c, b](s), -int(d == a))
            for ops, mod in ((signed, 0), (plain, 2)):
                ab, cd = ops[a, b], ops[c, d]
                lhs = (pair(ab, cd, s), 1), (pair(cd, ab, s), -1)
                require(
                    combine(*lhs, modulus=mod) == combine(*rhs, modulus=mod),
                    (a, b, c, d, s, mod, "commutator"),
                )


def gf2_rank(rows: list[int]) -> int:
    pivots: dict[int, int] = {}
    for row in rows:
        while row:
            pivot = row.bit_length() - 1
            if pivot not in pivots:
                pivots[pivot] = row
                break
            row ^= pivots[pivot]
    return len(pivots)


def check_triangles(
    n: int, k: int, states: list[int], signed: Transfers, plain: Transfers
) -> int:
    edges = [
        edge for edge in combinations(states, 2) if (edge[0] ^ edge[1]).bit_count() == 2
    ]
    edge_rows = {frozenset(edge): 1 << idx for idx, edge in enumerate(edges)}
    reached = {states[0]}
    while True:
        expanded = reached | {
            v for edge in edges if reached.intersection(edge) for v in edge
        }
        if expanded == reached:
            break
        reached = expanded
    require(reached == set(states), (n, k, "connectedness"))
    triangles = {}
    for triple in combinations(states, 3):
        row = [edge_rows.get(frozenset(e), 0) for e in combinations(triple, 2)]
        if all(row):
            triangles[frozenset(triple)] = sum(row)
    seen: set[frozenset[int]] = set()
    for i, j, ell in permutations(range(n), 3):
        for s in states:
            key = (s, i, j, ell)
            direct, un_direct = signed[i, ell](s), plain[i, ell](s)
            left = pair(signed[i, j], signed[j, ell], s)
            right = pair(signed[j, ell], signed[i, j], s)
            ul, ur = (
                pair(plain[i, j], plain[j, ell], s),
                pair(plain[j, ell], plain[i, j], s),
            )
            require(
                combine((ul, 1), (ur, 1)) == combine((un_direct, 1)),
                (key, "unsigned anticommutator"),
            )
            z_j = sign(occupied(s, j))
            require(
                combine((ul, 1), (ur, -1)) == combine((un_direct, z_j)),
                (key, "Z_j-twisted unsigned commutator"),
            )
            if direct is None:
                require(left is None and right is None, (key, "disabled paths"))
                continue
            first, indirect, disabled = (
                (signed[j, ell](s), left, right)
                if z_j == 1
                else (signed[i, j](s), right, left)
            )
            if first is None or indirect is None:
                raise AssertionError((key, "missing enabled path"))
            path_vertices = frozenset((s, first[0], direct[0]))
            seen.add(path_vertices)
            require(
                path_vertices in triangles and disabled is None,
                (key, "triangle coverage"),
            )
            require(indirect[0] == direct[0] and indirect[1] * direct[1] == z_j, key)
    require(seen == set(triangles), (n, k, "every Johnson triangle"))
    rank = gf2_rank(list(triangles.values()))
    # The connected graph's vertex sign switches span the V-1-dimensional kernel.
    require(rank == len(edges) - len(states) + 1, (n, k, rank, "cycle rank"))
    return rank


def check_orderings(
    n: int, states: list[int], signed: Transfers, plain: Transfers
) -> None:
    slots = range(n)
    for ordering in permutations(slots):
        ranks = tuple(ordering.index(slot) for slot in slots)
        inversions = [(a, b) for a, b in combinations(slots, 2) if ranks[a] > ranks[b]]
        phases = {
            s: sign(sum(occupied(s, a) * occupied(s, b) for a, b in inversions))
            for s in states
        }
        reordered_masks = {
            s: sum(occupied(s, h) << ranks[h] for h in slots) for s in states
        }
        for (i, j), action in signed.items():
            for s in states:
                out = action(s)
                unsigned = plain[i, j](s)
                require((out is None) == (unsigned is None), (s, i, j, "support"))
                if out is None:
                    continue
                dest, coefficient = out
                require(
                    unsigned == (dest, abs(coefficient)), (s, i, j, "basis populations")
                )
                require(
                    signed[j, i](dest) == (s, coefficient), (s, i, j, "reciprocity")
                )
                reordered = sign(between(reordered_masks[s], ranks[i], ranks[j]))
                require(
                    reordered == phases[dest] * coefficient * phases[s],
                    (s, i, j, ordering),
                )


def run_loop(ops: Transfers, state: int, moves: tuple[tuple[int, int], ...]) -> int:
    here, result = state, 1
    for move in moves:
        out = ops[move](here)
        if out is None:
            raise AssertionError((state, moves, move, "disabled loop step"))
        here, coefficient = out
        result *= coefficient
    require(here == state, (state, moves, "not closed"))
    return result


def spectator_control() -> None:
    # Same directed labels; the legal chronological order reverses the first two.
    loops = ((0b1100, ((1, 2), (0, 1), (2, 0))), (0b0110, ((0, 1), (1, 2), (2, 0))))
    signed, plain = transfers(4, True), transfers(4, False)
    signs = [run_loop(signed, s, moves) for s, moves in loops]
    unsigned = [run_loop(plain, s, moves) for s, moves in loops]
    require(signs == [1, -1] and unsigned == [1, 1], (signs, unsigned))
    print("J(4,2) empty/occupied middle loops: +1/-1, ratio -1; unsigned +1/+1.")
    print("Same basis populations; physical loop-sign detection needs coherence.")


def creation(slot: int, twisted: bool, state: int) -> Term:
    if occupied(state, slot):
        return None
    lower_mask = (1 << slot) - 1
    twist = -1 if twisted and state == 0b0001 else 1
    return state | (1 << slot), twist * sign((state & lower_mask).bit_count())


def annihilation(slot: int, twisted: bool, state: int) -> Term:
    if not occupied(state, slot):
        return None
    lower = state ^ (1 << slot)
    up = creation(slot, twisted, lower)
    if up is None or up[0] != state:
        raise AssertionError((slot, lower, state, "adjoint"))
    return lower, up[1]


def adjacent_sector_countermodel() -> None:
    n = 4
    exterior = transfers(n, True)
    create = [
        [partial(creation, i, twist) for i in range(n)] for twist in (False, True)
    ]
    destroy = [
        [partial(annihilation, i, twist) for i in range(n)] for twist in (False, True)
    ]
    bad: dict[tuple[int, int, int], dict[int, int]] = {}
    for i, j, s in product(range(n), range(n), range(1 << n)):
        for up, down in zip(create, destroy, strict=True):
            require(
                pair(up[i], down[j], s) == exterior[i, j](s),
                (i, j, s, "all transfers agree"),
            )
        ordered = [(pair(up[i], up[j], s), pair(up[j], up[i], s)) for up in create]
        if (i, j, s) == (0, 1, 0):
            require(ordered == [((3, 1), (3, -1)), ((3, 1), (3, 1))], ordered)
        standard, twisted = (combine((ab, 1), (ba, 1)) for ab, ba in ordered)
        require(not standard, (i, j, s, "exterior creation anticommutator"))
        if twisted:
            bad[i, j, s] = twisted
        for base_path, twisted_path in zip(*ordered, strict=True):
            require(
                combine((base_path, 1), modulus=2)
                == combine((twisted_path, 1), modulus=2),
                (i, j, s, "adjacent-sector char2 control"),
            )
    require(
        set(bad) == {(i, j, 0) for i, j in permutations(range(n), 2) if 0 in (i, j)},
        bad,
    )
    require(bad[0, 1, 0] == {0b0011: 2}, bad)
    total = n**2 * (1 << n)
    print(f"Adjacent sectors: all {total} Eij entries agree per model, including Eii.")
    print(f"All {total} ordered creation cases: {len(bad)} twisted CAR failures.")
    print("Vacuum square: exterior -1, twisted +1; {C0+,C1+}|empty> = 2|{0,1}>.")
    print("Char 2 control: coefficient signs collapse; the lifts coincide mod 2.")


def main() -> None:
    for n, k, expected_rank in ((3, 1, 1), (3, 2, 1), (4, 2, 7), (5, 2, 21), (5, 4, 6)):
        states = [s for s in range(1 << n) if s.bit_count() == k]
        signed, plain = transfers(n, True), transfers(n, False)
        check_matrix_units(n, states, signed, plain)
        rank = check_triangles(n, k, states, signed, plain)
        require(rank == expected_rank, (n, k, rank, expected_rank))
        check_orderings(n, states, signed, plain)
        print(
            f"J({n},{k}): {n**4 * len(states)} commutator entries; triangle rank = cycle rank = {rank}; unique up to vertex signs."
        )
    spectator_control()
    adjacent_sector_countermodel()


if __name__ == "__main__":
    main()
