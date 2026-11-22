"""Can five centers form the incidence using no random update scheduler?

Each anonymous center already stores one matching of the other four marks.
In one supplied synchronous round it reads the multiplicities of its six
possible pairs at the other centers. No chart, random site, named anchor or
comparison of mark IDs is an input to its decision. An output here means an
actual collision-free table on the same marks, not its isomorphism class.
"""

from collections import Counter
from itertools import permutations, product

from scripts.probe_anonymous_midpoint_factory import BANK, Q, Stock, count, transform
from scripts.probe_affine_pulse_holdouts import need

STATES = tuple(product(range(3), repeat=5))
FRAMES = tuple(permutations(Q))


def votes(s: Stock) -> tuple[tuple[int, ...], ...]:
    claims = count(s)
    # Each of the other four centers supplies exactly one pair which
    # does not contain i; remove i's two self-votes before deciding.
    return tuple(
        tuple(
            sum(claims[p] for p in matching) - 2 * (j == s[i])
            for j, matching in enumerate(BANK[i])
        )
        for i in Q
    )


def move(s: Stock) -> Stock:
    result = list(s)
    for i, row in enumerate(votes(s)):
        k = s[i]
        need(min(row) >= 0 and sum(row) == 4, "foreign-claim accounting")
        if row[k]:
            available = [j for j in range(3) if j != k and row[j] > 0]
            if available:
                winners = [
                    j for j in available if row[j] == min(row[t] for t in available)
                ]
                if len(winners) == 1:
                    result[i] = winners[0]
    return tuple(result)


def main() -> None:
    sinks = {s for s in STATES if len(count(s)) == 10}
    relabel = {s: tuple(transform(s, p) for p in FRAMES) for s in STATES}
    nxt = {s: move(s) for s in STATES}
    need(len(sinks) == 6 and all(nxt[s] == s for s in sinks), "admissible table")
    need(
        all(
            nxt[t] == relabel[nxt[s]][j]
            for s in STATES
            for j, t in enumerate(relabel[s])
        ),
        "a change of names changed the rule",
    )
    permanent = []
    depths: Counter[int] = Counter()
    periods: Counter[int] = Counter()
    anchored = [0] * 5
    for s in STATES:
        # Every H_s-symmetric datum remains so under deterministic equivariant
        # evolution. If the output is an actual table on these marks, it must
        # be fixed by every such frame. The following obstruction does not
        # impose locality or a bound on the duration of the dynamics.
        stab = [j for j, t in enumerate(relabel[s]) if t == s]
        eligible = [t for t in sinks if all(relabel[t][j] == t for j in stab)]
        for k in range(5):
            kept = [j for j in stab if FRAMES[j][:k] == Q[:k]]
            anchored[k] += not any(all(relabel[t][j] == t for j in kept) for t in sinks)
        t = s
        clock: dict[Stock, int] = {}
        while t not in sinks and t not in clock:
            clock[t] = len(clock)
            t = nxt[t]
        need(bool(eligible) == (t in sinks), "rule failed to attain symmetry ceiling")
        if t in sinks:
            depths[len(clock)] += 1
        else:
            periods[len(clock) - clock[t]] += 1
            permanent.append((s, len(stab)))
    need(depths == {0: 6, 1: 12, 2: 180} and periods == {1: 15, 2: 30}, "basins")
    need(Counter(h for _, h in permanent) == {8: 15, 4: 30}, "obstructing stabilizers")
    need(anchored == [45, 21, 9, 3, 0], "anchor filtration")
    print(
        "Anonymous synchronous rule: 6 initially valid, 12 reached in one round, 180 in two."
    )
    print(
        "45 symmetry-obstructed inputs: 15 fixed and 30 on two-cycles; 198/243 attained."
    )
    print("No invariant terminal table after naming 0,1,2,3,4 fixed marks:", anchored)
    print(
        "Assumes five marks, initial matchings, foreign-claim access and common rounds; no physical selection."
    )


if __name__ == "__main__":
    main()
