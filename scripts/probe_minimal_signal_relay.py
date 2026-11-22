"""Finite marked-site relays versus an infinite rank-three interpretation.

Each relay has an actual finite site set and four reciprocal port transitions.
A signal moves by that site's transition table and reports whether it touches
one marked site. It never accumulates a virtual displacement as its readout.
The sites, reciprocal port names, transition tables, and marker/detection
capability are supplied; this probe does not derive their physical existence.

The 26-site cyclic difference-set graph meets the degree-four bipartite
girth-six Moore lower bound, but only C3 of the 24 global compass permutations
lifts. A 32-site quotient meets the two nominated six-tick tests and all S4
compass permutations, but has extra six-tick returns. A 64-site quotient has
exactly the infinite abelian model's nonbacktracking return language through
six ticks, while remaining finite.

The 32/64 minimality arguments below concern connected finite ABELIAN endpoint
quotients A3/L with a globally S4-invariant kernel and two alternating roles.
They are not universal lower bounds for all mechanisms or physical spaces.
Rank/bound arithmetic and finite exhaustive controls are not Lean proofs.
"""

from __future__ import annotations

from collections import deque
from dataclasses import dataclass
from itertools import pairwise, permutations, product
from math import gcd

Word = tuple[int, ...]
Point = tuple[int, ...]
PORTS = tuple(range(4))
COMPASS = tuple(permutations(PORTS))


def need(condition: bool, message: str) -> None:
    if not condition:
        raise ArithmeticError(message)


@dataclass(frozen=True)
class Relay:
    name: str
    neighbors: tuple[tuple[int, ...], ...]
    role: tuple[int, ...]

    def walk(self, start: int, word: Word) -> int:
        site = start
        for port in word:
            site = self.neighbors[site][port]
        return site

    def marked_return(self, marker: int, word: Word) -> bool:
        # One actual site remains marked. No endpoint-count oracle is used.
        return self.walk(marker, word) == marker


def cyclic_26() -> Relay:
    offsets = (0, 1, 3, 9)
    points = tuple(product(range(2), range(13)))
    index = {p: i for i, p in enumerate(points)}
    neighbors = tuple(
        tuple(index[1 - role, (x + (1 if role == 0 else -1) * d) % 13] for d in offsets)
        for role, x in points
    )
    differences = {(a - b) % 13 for a, b in product(offsets, repeat=2) if a != b}
    need(differences == set(range(1, 13)), "cyclic perfect difference set")
    return Relay("Z13 difference-set relay", neighbors, tuple(p[0] for p in points))


def quotient_4(diagonal: tuple[int, ...]) -> Relay:
    def canonical(point: Point) -> Point:
        return min(tuple((x + shift) % 4 for x in point) for shift in diagonal)

    points = tuple(
        sorted(
            {
                (sum(p) % 4, *canonical(p))
                for p in product(range(4), repeat=4)
                if sum(p) % 4 in (0, 1)
            }
        )
    )
    index = {p: i for i, p in enumerate(points)}
    neighbors: list[tuple[int, ...]] = []
    for p in points:
        role, coordinates = p[0], p[1:]
        targets: list[int] = []
        for port in PORTS:
            out = tuple(
                (x + (1 if role == 0 else -1) * int(i == port)) % 4
                for i, x in enumerate(coordinates)
            )
            targets.append(index[(1 - role, *canonical(out))])
        neighbors.append(tuple(targets))
    need(len(points) == 128 // len(diagonal), "diagonal quotient size")
    return Relay(
        f"A3 mod4 / diagonal {diagonal}", tuple(neighbors), tuple(p[0] for p in points)
    )


def nonbacktracking(length: int) -> tuple[Word, ...]:
    return tuple(
        w for w in product(PORTS, repeat=length) if all(a != b for a, b in pairwise(w))
    )


def graph_controls(relay: Relay) -> None:
    sites = range(len(relay.neighbors))
    for site in sites:
        need(len(set(relay.neighbors[site])) == 4, "four distinct local neighbors")
        for port, target in enumerate(relay.neighbors[site]):
            need(relay.role[target] != relay.role[site], "bipartite role change")
            need(relay.neighbors[target][port] == site, "reciprocal involutive port")
        shell2 = {
            relay.walk(site, (a, b)) for a, b in product(PORTS, repeat=2) if a != b
        }
        need(
            len(shell2) == 12 and site not in shell2,
            "faithful twelve-site two-tick shell",
        )
    reached = {0}
    pending = [0]
    while pending:
        for site in relay.neighbors[pending.pop()]:
            if site not in reached:
                reached.add(site)
                pending.append(site)
    need(len(reached) == len(relay.neighbors), "connected relay")
    for length in range(1, 6):
        for word in nonbacktracking(length):
            need(
                not any(relay.marked_return(site, word) for site in sites),
                "spurious nonbacktracking return below six ticks",
            )
    for a, b, c in permutations(PORTS, 3):
        need(
            all(relay.marked_return(site, (a, b, c) * 2) for site in sites),
            "abcabc reunion",
        )
    for a, b in permutations(PORTS, 2):
        need(
            not any(relay.marked_return(site, (a, b) * 3) for site in sites),
            "ababab must not reunite",
        )


def lifted_permutation(
    relay: Relay, compass: Word, origin_image: int
) -> tuple[int, ...] | None:
    # Connected colored graph: an image for one site uniquely forces every
    # other image. This exhausts arbitrary site bijections, not only affine
    # formulas, including maps that exchange the two roles.
    image = [-1] * len(relay.neighbors)
    image[0] = origin_image
    pending: deque[int] = deque([0])
    while pending:
        site = pending.popleft()
        for port, target in enumerate(relay.neighbors[site]):
            candidate = relay.neighbors[image[site]][compass[port]]
            if image[target] == -1:
                image[target] = candidate
                pending.append(target)
            elif image[target] != candidate:
                return None
    if len(set(image)) != len(image):
        return None
    return tuple(image)


def compass_controls(relay: Relay, expected: int) -> tuple[Word, ...]:
    allowed: list[Word] = []
    for compass in COMPASS:
        count = sum(
            lifted_permutation(relay, compass, site) is not None
            for site in range(len(relay.neighbors))
        )
        need(count in (0, len(relay.neighbors)), "unexpected partial origin orbit")
        if count:
            allowed.append(compass)
    need(len(allowed) == expected, "global compass group size")
    if expected == 3:
        need(
            set(allowed) == {(0, 1, 2, 3), (0, 2, 3, 1), (0, 3, 1, 2)},
            "cyclic relay lifts exactly C3",
        )
    return tuple(allowed)


def six_tick_language(relay: Relay, expected: int) -> tuple[Word, ...]:
    words = nonbacktracking(6)
    returned = tuple(w for w in words if relay.marked_return(0, w))
    for site in range(len(relay.neighbors)):
        need(
            tuple(w for w in words if relay.marked_return(site, w)) == returned,
            "return language depends on marker site",
        )
    need(len(returned) == expected, "six-tick return count")
    native = {w + w for w in permutations(PORTS, 3)}
    need(native <= set(returned), "missing native six-word")
    if expected == 24:
        need(set(returned) == native, "extra six-tick relation")
    return returned


def moore_control(relay: Relay) -> int:
    # For degree4 girth6, grow depth2 on either side of an edge, without
    # crossing it. Any repeated site would create a cycle of length<=5.
    u, v = 0, relay.neighbors[0][0]
    left1 = set(relay.neighbors[u]) - {v}
    right1 = set(relay.neighbors[v]) - {u}
    left2 = {z for x in left1 for z in relay.neighbors[x] if z != u}
    right2 = {z for x in right1 for z in relay.neighbors[x] if z != v}
    parts = ({u}, {v}, left1, right1, left2, right2)
    need(tuple(map(len, parts)) == (1, 1, 3, 3, 9, 9), "edge-rooted Moore layers")
    need(
        sum(map(len, parts)) == len(set().union(*parts)) == 26,
        "Moore layer disjointness",
    )
    return 26


def conditional_bound_controls() -> None:
    # Let L be S4-stable in A3 and m the common root order in A3/L.
    # Then m*A3 <= L. For x in L, x-(ij)x=(xi-xj)(ei-ej) is in L,
    # so every xi-xj is divisible by m. Thus L/m*A3 is contained in
    # the diagonal subgroup, whose size is gcd(m,4). Consequently
    # |A3/L| >= m^3/gcd(m,4). Faithful two-tick tests exclude m<=2;
    # ababab exclusion rules out m=3. For m>=4 the bound is >=16.
    # These arguments are stated assumptions/algebra, not a Lean artifact.
    for m in range(4, 129):
        diagonal_count = sum(4 * t % m == 0 for t in range(m))
        need(diagonal_count == gcd(m, 4), "diagonal subgroup arithmetic")
        need(m**3 // diagonal_count >= 16, "32-site conditional lower bound")
        if m >= 5:
            need(m**3 // diagonal_count >= 32, "larger root order cannot improve 64")
    need(4**3 // 4 == 16 and 4**3 // 2 == 32, "sharp quotient sizes")
    # For the full six-word language, m=4's order-four diagonal subgroup
    # identifies (-3,1,1,1) with zero, adding a length-six path. Therefore
    # only the order-two subgroup or smaller remains, requiring64 sites.
    bad = (-3, 1, 1, 1)
    need(
        sum(bad) == 0 and sum(map(abs, bad)) == 6 and {x % 4 for x in bad} == {1},
        "new six-tick kernel witness",
    )
    # The order-two diagonal kernel has no nonzero vector with l1<=6.
    for x in product(range(-3, 4), repeat=4):
        if sum(x) == 0 and sum(map(abs, x)) <= 6:
            in_kernel = len({i % 4 for i in x}) == 1 and x[0] % 4 in (0, 2)
            need(
                not in_kernel or x == (0, 0, 0, 0),
                "short kernel vector in 64-site rival",
            )


def main() -> None:
    relays = (
        cyclic_26(),
        quotient_4((0, 1, 2, 3)),
        quotient_4((0, 2)),
        quotient_4((0,)),
    )
    expected = ((3, 108), (24, 72), (24, 24), (24, 24))
    for relay, (compass_count, return_count) in zip(relays, expected, strict=True):
        graph_controls(relay)
        lifts = compass_controls(relay, compass_count)
        returns = six_tick_language(relay, return_count)
        moore_control(relay)
        print(
            f"{len(relay.neighbors)} sites: global compass permutations={len(lifts)}/24; six-tick nonbacktracking returns={len(returns)}; local marker/ports pass."
        )
    need(
        bool(
            set(six_tick_language(relays[1], 72))
            - set(six_tick_language(relays[2], 24))
        ),
        "32 versus64 discriminator missing",
    )
    extra = (1, 0, 2, 0, 3, 0)
    need(
        relays[1].marked_return(0, extra) and not relays[2].marked_return(0, extra),
        "explicit extra six-tick reunion",
    )
    conditional_bound_controls()
    print(
        "26 meets the unrestricted degree4 bipartite girth6 Moore bound, but lacks full S4 global compass symmetry."
    )
    print(
        "Conditional abelian/S4 minima:32 sites for nominated abcabc/ababab tests;64 for the full six-tick return language."
    )
    print(
        "32-site extra return (1,0,2,0,3,0) distinguishes it from64 and the infinite endpoint quotient."
    )
    print(
        "All witnesses are finite marked-site transition systems. Endpoint rules, coherent port names, marker and detection remain supplied; no physical dimension or infinite space follows."
    )


if __name__ == "__main__":
    main()
